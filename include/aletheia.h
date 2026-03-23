/*
 * Aletheia C API
 *
 * Formally verified CAN frame analysis via Linear Temporal Logic.
 * This header defines the C ABI exported by libaletheia-ffi.so.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#ifndef ALETHEIA_H
#define ALETHEIA_H

#ifdef __cplusplus
extern "C" {
#endif

/*
 * GHC Runtime System initialization.
 *
 * Must be called exactly once per process, before any aletheia_* calls.
 * argc and argv may be NULL/0 for default RTS options.
 *
 * IMPORTANT: Never call hs_exit() after hs_init(). The GHC RTS does not
 * support reinitialization — calling hs_exit() followed by hs_init() will
 * crash. The RTS is cleaned up automatically at process exit.
 */
void hs_init(int *argc, char ***argv);

/*
 * Create a new Aletheia session.
 *
 * Returns an opaque state handle for use with aletheia_process().
 * Each session maintains independent LTL evaluation state — multiple
 * sessions may run concurrently from separate threads.
 *
 * The handle must be freed with aletheia_close() when no longer needed.
 */
void *aletheia_init(void);

/*
 * Process a JSON command and return the response.
 *
 * @param state   Handle from aletheia_init(). Must not be NULL.
 * @param input   UTF-8 encoded, null-terminated JSON string.
 * @return        UTF-8 encoded, null-terminated JSON response.
 *                The caller MUST free the returned string with
 *                aletheia_free_str(). Returns NULL only on allocation failure.
 *
 * Thread safety: A single state handle must not be used from multiple threads
 * concurrently. Different state handles may be used from different threads.
 *
 * See the Aletheia JSON protocol documentation for command/response formats.
 */
char *aletheia_process(void *state, const char *input);

/*
 * Free a string returned by aletheia_process().
 *
 * @param ptr   String pointer returned by aletheia_process().
 *              Passing NULL is safe (no-op).
 */
void aletheia_free_str(char *ptr);

/*
 * Close a session and free its state.
 *
 * @param state   Handle from aletheia_init().
 *                The handle must not be used after this call.
 */
void aletheia_close(void *state);

#ifdef __cplusplus
}
#endif

#endif /* ALETHEIA_H */
