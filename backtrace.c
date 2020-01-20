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

static DWORD64 WINAPI MyGetModuleBase64(
        _In_  HANDLE hProcess,
        _In_  DWORD64 dwAddr)
{
    (void)hProcess;
    UNWIND_HISTORY_TABLE HistoryTable = {0};
    DWORD64 ImageBase = 0;
    RtlLookupFunctionEntry(dwAddr, &ImageBase, &HistoryTable);
    return ImageBase;
}

static PVOID CALLBACK MyFunctionTableAccess64(
        _In_  HANDLE hProcess,
        _In_  DWORD64 AddrBase)
{
    (void)hProcess;
    UNWIND_HISTORY_TABLE HistoryTable = {0};
    DWORD64 ImageBase;
    return RtlLookupFunctionEntry(AddrBase, &ImageBase, &HistoryTable);

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
typedef enum {
    AddrMode1616,
    AddrMode1632,
    AddrModeReal,
    AddrModeFlat
  } ADDRESS_MODE;

typedef struct _tagADDRESS64 {
    DWORD64 Offset;
    WORD Segment;
    ADDRESS_MODE Mode;
  } ADDRESS64,*LPADDRESS64;

typedef struct _KDHELP64 {
    DWORD64 Thread;
    DWORD ThCallbackStack;
    DWORD ThCallbackBStore;
    DWORD NextCallback;
    DWORD FramePointer;
    DWORD64 KiCallUserMode;
    DWORD64 KeUserCallbackDispatcher;
    DWORD64 SystemRangeStart;
    DWORD64 KiUserExceptionDispatcher;
    DWORD64 StackBase;
    DWORD64 StackLimit;
    DWORD64 Reserved[5];
  } KDHELP64,*PKDHELP64;

typedef struct _tagSTACKFRAME64 {
    ADDRESS64 AddrPC;
    ADDRESS64 AddrReturn;
    ADDRESS64 AddrFrame;
    ADDRESS64 AddrStack;
    ADDRESS64 AddrBStore;
    PVOID FuncTableEntry;
    DWORD64 Params[4];
    WINBOOL Far;
    WINBOOL Virtual;
    DWORD64 Reserved[3];
    KDHELP64 KdHelp;
  } STACKFRAME64,*LPSTACKFRAME64;

struct stack_info
{
    CONTEXT c;
    STACKFRAME64 sf;		 /* For storing the stack information */
};

static void stack_info_init(struct stack_info *si, PUINT_PTR framep, PCONTEXT ctx)
{
    memset (si, 0, sizeof *si);

    memcpy (&si->c, ctx, sizeof si->c);
    
    memset (&si->sf, 0, sizeof (si->sf));
    
    si->sf.AddrFrame.Offset = (UINT_PTR) framep;
    si->sf.AddrReturn.Offset = framep[1];

    si->sf.AddrPC.Mode = AddrModeFlat;
    si->sf.AddrFrame.Mode = AddrModeFlat;
    si->sf.AddrStack.Mode = AddrModeFlat;    
}

static inline void
__unwind_single_frame (PCONTEXT ctx)
{
  PRUNTIME_FUNCTION f;
  ULONG64 imagebase;
  UNWIND_HISTORY_TABLE hist = {0};
  DWORD64 establisher;
  PVOID hdl;

  f = RtlLookupFunctionEntry (ctx->Rip, &imagebase, &hist);
  if (f) {
    RtlVirtualUnwind (0, imagebase, ctx->Rip, f, ctx, &hdl, &establisher,
		      NULL);
  }
  else {
      ctx->Rip = *(ULONG_PTR *) ctx->Rsp;
      ctx->Rsp += 8;
  }
}

static int stack_info_walk(struct stack_info *si)
{
    if (!si->c.Rip) {
        printf("DONE: si->c.Rsp: %p, si->c.Rbp : %p\n",  (void*)si->c.Rsp,  (void*)si->c.Rbp);
        return 0;
    }

    printf("WALK: si->c.Rip: %p, si->c.Rsp: %p, si->c.Rbp : %p, Rip readable: %d, Rsp readable: %d\n", (void*)si->c.Rip,  (void*)si->c.Rsp,  (void*)si->c.Rbp,
           readable_pointer((LPCVOID)si->c.Rip),
           readable_pointer((LPCVOID)si->c.Rsp)
    );
    if ( readable_pointer((LPCVOID)si->c.Rsp)) {
        DWORD64 *sptr = (DWORD64*)si->c.Rsp;
        sptr -= 4;
        printf("sptr[0]=%p, sptr[1]=%p, sptr[2]=%p, sptr[3]=%p, sptr[4]=%p, sptr[5]=%p\n",
                (void*)sptr[0],  (void*)sptr[1],  (void*)sptr[2],  (void*)sptr[3],  (void*)sptr[4],  (void*)sptr[5]);
    }
    si->sf.AddrPC.Offset    = si->c.Rip;
    si->sf.AddrStack.Offset = si->c.Rsp;
    si->sf.AddrFrame.Offset = si->c.Rbp;
    
    __unwind_single_frame (&si->c);
  
    return 1;
}


int cygwin_backtrace (void **array, int size);

static void *frames[16];

int __attribute__((noinline))
backtrace_full (struct backtrace_state *state, int skip,
		backtrace_full_callback callback,
		backtrace_error_callback error_callback, void *data)
{
    int size = cygwin_backtrace(frames, 16);
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
    int i;
    char module_name_raw[MAX_PATH];
    HANDLE process = GetCurrentProcess();
    for (i = skip + 1; i < size; i++) {
        DWORD64 ImageBase = MyGetModuleBase64(process, frames[i]);
        if (ImageBase && GetModuleFileNameA((HINSTANCE)ImageBase, module_name_raw, MAX_PATH)) {
            state->filename = module_name_raw;
        }
        unwind((uintptr_t)frames[i], &bdata);        
    }

// New
#if 0    
      CONTEXT c;
    memset (&c, 0, sizeof c);
    c.ContextFlags = CONTEXT_FULL;
    RtlCaptureContext (&c);

    struct stack_info si;
    stack_info_init(&si, (PUINT_PTR) c.Rbp, &c);
  
    int i;
    for (i = 0; i < 32 && stack_info_walk(&si); i++)
    {
        printf("%d %p %p\n", i,  (void*)si.sf.AddrFrame.Offset,  (void*)si.sf.AddrPC.Offset);
    }
#endif    


#if 0
    CONTEXT context = {};
    context.ContextFlags = CONTEXT_FULL;

    RtlCaptureContext(&context);
    CONTEXT cursor = context;
    int i = skip + 1;
    char module_name_raw[MAX_PATH];
    while (1) {
        uintptr_t *ip =  (uintptr_t*)cursor.Rip;
        uintptr_t *sp =  (uintptr_t*)cursor.Rsp;

        // if (*ip == 0) {
        //     if (!readable_pointer((LPCVOID)*sp))
        //         break;
        //     cursor.Rip = *(DWORD64*)*sp;      // POP RIP (aka RET)
        //     cursor.Rsp += sizeof(void*);
        //     if (cursor.Rip == 0) {
                
        //         break;
        //     }
        // }
        
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
 
            // cursor.Rsp = cursor.Rbp;                 // MOV RSP, RBP
            // if (!readable_pointer((LPCVOID)cursor.Rsp))
            //     break;
            // cursor.Rbp = *(DWORD64*)cursor.Rsp;      // POP RBP
            // cursor.Rsp += sizeof(void*);
            // cursor.Rip = *(DWORD64*)cursor.Rsp;      // POP RIP (aka RET)
            // cursor.Rsp += sizeof(void*);
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
#endif
    
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
