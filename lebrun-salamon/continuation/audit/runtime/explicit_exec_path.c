/* Portable executable discovery for the unchanged Lean executable.
 * For the current process only, supply an explicitly configured application
 * path. No /proc path is accessed by this branch. All other readlink calls
 * retain libc behavior; the Lean executable and shared libraries are untouched.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>

ssize_t readlink(const char *path, char *buffer, size_t capacity) {
    const char *configured = getenv("LEAN_EXPLICIT_EXECUTABLE");
    if (configured != NULL && configured[0] == '/') {
        char own_exe[80];
        snprintf(own_exe, sizeof own_exe, "/proc/%ld/exe", (long)getpid());
        if (strcmp(path, own_exe) == 0) {
            size_t length = strlen(configured);
            if (length > capacity) length = capacity;
            memcpy(buffer, configured, length);
            return (ssize_t)length;
        }
    }
    ssize_t (*original)(const char *, char *, size_t) = dlsym(RTLD_NEXT, "readlink");
    if (original == NULL) { errno = ENOSYS; return -1; }
    return original(path, buffer, capacity);
}
