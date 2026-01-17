//===- lib/Support/ErrorHandling.cpp - Callbacks for errors ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines an API used to indicate fatal error conditions.  Non-fatal
// errors (most of them) should be handled through LLVMContext.
//
//===----------------------------------------------------------------------===//

#include "llvm/Support/ErrorHandling.h"
#include <cassert>
#include <cstdlib>
#include <mutex>
#include <iostream>
#include <new>

using namespace llvm;

static fatal_error_handler_t ErrorHandler = nullptr;
static void *ErrorHandlerUserData = nullptr;

static fatal_error_handler_t BadAllocErrorHandler = nullptr;
static void *BadAllocErrorHandlerUserData = nullptr;

void llvm::install_fatal_error_handler(fatal_error_handler_t handler,
                                       void *user_data) {
#if LLVM_ENABLE_THREADS == 1
  std::lock_guard<std::mutex> Lock(ErrorHandlerMutex);
#endif
  assert(!ErrorHandler && "Error handler already registered!\n");
  ErrorHandler = handler;
  ErrorHandlerUserData = user_data;
}

void llvm::remove_fatal_error_handler() {
#if LLVM_ENABLE_THREADS == 1
  std::lock_guard<std::mutex> Lock(ErrorHandlerMutex);
#endif
  ErrorHandler = nullptr;
  ErrorHandlerUserData = nullptr;
}

void llvm::report_fatal_error(const char *Reason, bool GenCrashDiag) {
  llvm::fatal_error_handler_t handler = nullptr;
  void* handlerData = nullptr;
  {
    // Only acquire the mutex while reading the handler, so as not to invoke a
    // user-supplied callback under a lock.
#if LLVM_ENABLE_THREADS == 1
    std::lock_guard<std::mutex> Lock(ErrorHandlerMutex);
#endif
    handler = ErrorHandler;
    handlerData = ErrorHandlerUserData;
  }

  if (handler) {
    handler(handlerData, Reason, GenCrashDiag);
  } else {
    // No handler, just print the message.
    fprintf(stderr, "Fatal error: %s\n", Reason);
  }

  // If we reached here, we are failing ungracefully. Run the interrupt handlers
  // to make sure any special cleanups get done, in particular that we remove
  // files registered with RemoveFileOnSignal.
  if (GenCrashDiag)
    abort();
  else
    exit(1);
}

void llvm::reportFatalInternalError(const char *reason) {
  report_fatal_error(reason, /*GenCrashDiag=*/true);
}
void llvm::reportFatalUsageError(const char *reason) {
  report_fatal_error(reason, /*GenCrashDiag=*/false);
}

void llvm::install_bad_alloc_error_handler(fatal_error_handler_t handler,
                                           void *user_data) {
#if LLVM_ENABLE_THREADS == 1
  std::lock_guard<std::mutex> Lock(BadAllocErrorHandlerMutex);
#endif
  assert(!BadAllocErrorHandler &&
         "Bad alloc error handler already registered!\n");
  BadAllocErrorHandler = handler;
  BadAllocErrorHandlerUserData = user_data;
}

void llvm::remove_bad_alloc_error_handler() {
#if LLVM_ENABLE_THREADS == 1
  std::lock_guard<std::mutex> Lock(BadAllocErrorHandlerMutex);
#endif
  BadAllocErrorHandler = nullptr;
  BadAllocErrorHandlerUserData = nullptr;
}

void llvm::report_bad_alloc_error(const char *Reason, bool GenCrashDiag) {
  fatal_error_handler_t Handler = nullptr;
  void *HandlerData = nullptr;
  {
    // Only acquire the mutex while reading the handler, so as not to invoke a
    // user-supplied callback under a lock.
#if LLVM_ENABLE_THREADS == 1
    std::lock_guard<std::mutex> Lock(BadAllocErrorHandlerMutex);
#endif
    Handler = BadAllocErrorHandler;
    HandlerData = BadAllocErrorHandlerUserData;
  }

  if (Handler) {
    Handler(HandlerData, Reason, GenCrashDiag);
    llvm_unreachable("bad alloc handler should not return");
  }

#ifdef LLVM_ENABLE_EXCEPTIONS
  // If exceptions are enabled, make OOM in malloc look like OOM in new.
  throw std::bad_alloc();
#else
  fprintf(stderr, "Fatal error: %s\n", Reason);
  abort();
#endif
}

#ifdef LLVM_ENABLE_EXCEPTIONS
// Do not set custom new handler if exceptions are enabled. In this case OOM
// errors are handled by throwing 'std::bad_alloc'.
void llvm::install_out_of_memory_new_handler() {
}
#else
// Causes crash on allocation failure. It is called prior to the handler set by
// 'install_bad_alloc_error_handler'.
static void out_of_memory_new_handler() {
  llvm::report_bad_alloc_error("Allocation failed");
}

// Installs new handler that causes crash on allocation failure. It is called by
// InitLLVM.
void llvm::install_out_of_memory_new_handler() {
  std::new_handler old = std::set_new_handler(out_of_memory_new_handler);
  (void)old;
  assert((old == nullptr || old == out_of_memory_new_handler) &&
         "new-handler already installed");
}
#endif

void llvm::llvm_unreachable_internal(const char *msg, const char *file,
                                     unsigned line) {
  const auto &dbgs = []() -> std::ostream & {
    return std::cerr;
  };

  // This code intentionally doesn't call the ErrorHandler callback, because
  // llvm_unreachable is intended to be used to indicate "impossible"
  // situations, and not legitimate runtime errors.
  if (msg)
    dbgs() << msg << "\n";
  dbgs() << "UNREACHABLE executed";
  if (file)
    dbgs() << " at " << file << ":" << line;
  dbgs() << "!\n";
  abort();
#ifdef LLVM_BUILTIN_UNREACHABLE
  // Windows systems and possibly others don't declare abort() to be noreturn,
  // so use the unreachable builtin to avoid a Clang self-host warning.
  LLVM_BUILTIN_UNREACHABLE;
#endif
}
