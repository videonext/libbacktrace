/* backtrace.c -- Entry point for stack backtrace library.
   Copyright (C) 2012-2019 Free Software Foundation, Inc.
   Written by Ian Lance Taylor, Google.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

    (1) Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.

    (2) Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in
    the documentation and/or other materials provided with the
    distribution.

    (3) The name of the author may not be used to
    endorse or promote products derived from this software without
    specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.  */

#include "config.h"

#include <sys/types.h>

#include "unwind.h"
#include "backtrace.h"
#include "internal.h"

/* The main backtrace_full routine.  */

/* Data passed through _Unwind_Backtrace.  */

struct backtrace_data
{
  /* Number of frames to skip.  */
  int skip;
  /* Library state.  */
  struct backtrace_state *state;
  /* Callback routine.  */
  backtrace_full_callback callback;
  /* Error callback routine.  */
  backtrace_error_callback error_callback;
  /* Data to pass to callback routines.  */
  void *data;
  /* Value to return from backtrace_full.  */
  int ret;
  /* Whether there is any memory available.  */
  int can_alloc;
};

#ifdef __CYGWIN__
#include <windows.h>

static _Unwind_Reason_Code
unwind (uintptr_t pc, void *vdata)
{
  struct backtrace_data *bdata = (struct backtrace_data *) vdata;

  if (!bdata->can_alloc)
    bdata->ret = bdata->callback (bdata->data, pc, NULL, 0, NULL);
  else
    bdata->ret = backtrace_pcinfo (bdata->state, pc, bdata->callback,
				   bdata->error_callback, bdata->data);
  if (bdata->ret != 0)
    return _URC_END_OF_STACK;

  return _URC_NO_REASON;
}

static int readable_pointer(LPCVOID pointer)
{
    // Check whether the pointer is valid and executable before dereferencing
    // to avoid segfault while recording. See #10638.
    MEMORY_BASIC_INFORMATION mInfo;
    if (VirtualQuery(pointer, &mInfo, sizeof(MEMORY_BASIC_INFORMATION)) == 0)
        return 0;
    DWORD X = mInfo.AllocationProtect;
    if (!((X&PAGE_READONLY) || (X&PAGE_READWRITE) || (X&PAGE_WRITECOPY) || (X&PAGE_EXECUTE_READ)) ||
          (X&PAGE_GUARD) || (X&PAGE_NOACCESS))
        return 0;
    return 1;
}

static UNWIND_HISTORY_TABLE HistoryTable;
static DWORD64 WINAPI MyGetModuleBase64(
        _In_  HANDLE hProcess,
        _In_  DWORD64 dwAddr)
{
    (void)hProcess;
    DWORD64 ImageBase = 0;
    RtlLookupFunctionEntry(dwAddr, &ImageBase, &HistoryTable);
    return ImageBase;
}

static PVOID CALLBACK MyFunctionTableAccess64(
        _In_  HANDLE hProcess,
        _In_  DWORD64 AddrBase)
{
    (void)hProcess;
    DWORD64 ImageBase;
    return RtlLookupFunctionEntry(AddrBase, &ImageBase, &HistoryTable);
}


int __attribute__((noinline))
backtrace_full (struct backtrace_state *state, int skip,
		backtrace_full_callback callback,
		backtrace_error_callback error_callback, void *data)
{
    struct backtrace_data bdata;
    void *p;

    bdata.skip = skip + 1;
    bdata.state = state;
    bdata.callback = callback;
    bdata.error_callback = error_callback;
    bdata.data = data;
    bdata.ret = 0;

    /* If we can't allocate any memory at all, don't try to produce
       file/line information.  */
    p = backtrace_alloc (state, 4096, NULL, NULL);
    if (p == NULL)
        bdata.can_alloc = 0;
    else
    {
        backtrace_free (state, p, 4096, NULL, NULL);
        bdata.can_alloc = 1;
    }

    CONTEXT context = {};
    RtlCaptureContext(&context);
    CONTEXT cursor = context;
    int i = skip + 1;
    char module_name_raw[MAX_PATH];
    while (1) {        
        uintptr_t *ip =  (uintptr_t*)cursor.Rip;
        uintptr_t *sp =  (uintptr_t*)cursor.Rsp;

        if (*ip == 0) {
            if (!readable_pointer((LPCVOID)*sp))
                break;
            cursor.Rip = *(DWORD64*)*sp;      // POP RIP (aka RET)
            cursor.Rsp += sizeof(void*);
            if (cursor.Rip == 0)
                break;
        }
        
        DWORD64 ImageBase = MyGetModuleBase64(GetCurrentProcess(), cursor.Rip);

        if (!ImageBase)
            break;
        
        PRUNTIME_FUNCTION FunctionEntry = (PRUNTIME_FUNCTION)MyFunctionTableAccess64(
            GetCurrentProcess(), cursor.Rip);

        if (GetModuleFileNameA((HINSTANCE)ImageBase, module_name_raw, MAX_PATH)) {
            state->filename = module_name_raw;
        } else {
            state->filename = "[unknown module]";
        }

//        fprintf(stderr, "ip: %p (%d); sp: %p (%d) base: %p, name: %s\n", ip, *ip,  sp, *sp, ImageBase, module_name);
        
        if (i-- <= 0)
            unwind((uintptr_t)ip, &bdata);
        
        if (!FunctionEntry) { // assume this is a NO_FPO RBP-based function
            cursor.Rsp = cursor.Rbp;                 // MOV RSP, RBP
            if (!readable_pointer((LPCVOID)cursor.Rsp))
                break;
            cursor.Rbp = *(DWORD64*)cursor.Rsp;      // POP RBP
            cursor.Rsp += sizeof(void*);
            cursor.Rip = *(DWORD64*)cursor.Rsp;      // POP RIP (aka RET)
            cursor.Rsp += sizeof(void*);
        }
        else {
            PVOID HandlerData;
            DWORD64 EstablisherFrame;
            (void)RtlVirtualUnwind(
                0 /*UNW_FLAG_NHANDLER*/,
                ImageBase,
                cursor.Rip,
                FunctionEntry,
                &cursor,
                &HandlerData,
                &EstablisherFrame,
                NULL);
        }
        if (cursor.Rip == 0)
            break;        
    }
  
    return bdata.ret;
}
#else
/* Unwind library callback routine.  This is passed to
   _Unwind_Backtrace.  */

static _Unwind_Reason_Code
unwind (struct _Unwind_Context *context, void *vdata)
{
  struct backtrace_data *bdata = (struct backtrace_data *) vdata;
  uintptr_t pc;
  int ip_before_insn = 0;

#ifdef HAVE_GETIPINFO
  pc = _Unwind_GetIPInfo (context, &ip_before_insn);
#else
  pc = _Unwind_GetIP (context);
#endif

  if (bdata->skip > 0)
    {
      --bdata->skip;
      return _URC_NO_REASON;
    }

  if (!ip_before_insn)
    --pc;

  if (!bdata->can_alloc)
    bdata->ret = bdata->callback (bdata->data, pc, NULL, 0, NULL);
  else
    bdata->ret = backtrace_pcinfo (bdata->state, pc, bdata->callback,
				   bdata->error_callback, bdata->data);
  if (bdata->ret != 0)
    return _URC_END_OF_STACK;

  return _URC_NO_REASON;
}

/* Get a stack backtrace.  */

int __attribute__((noinline))
backtrace_full (struct backtrace_state *state, int skip,
		backtrace_full_callback callback,
		backtrace_error_callback error_callback, void *data)
{
  struct backtrace_data bdata;
  void *p;

  bdata.skip = skip + 1;
  bdata.state = state;
  bdata.callback = callback;
  bdata.error_callback = error_callback;
  bdata.data = data;
  bdata.ret = 0;

  /* If we can't allocate any memory at all, don't try to produce
     file/line information.  */
  p = backtrace_alloc (state, 4096, NULL, NULL);
  if (p == NULL)
    bdata.can_alloc = 0;
  else
    {
      backtrace_free (state, p, 4096, NULL, NULL);
      bdata.can_alloc = 1;
    }

  _Unwind_Backtrace (unwind, &bdata);
  return bdata.ret;
}
#endif
