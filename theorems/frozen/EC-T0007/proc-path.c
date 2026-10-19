#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
/* This host denies /proc/<pid>/exe but permits the equivalent /proc/self/exe.
   Redirect only the running process's executable-path query. */
ssize_t readlink(const char *path, char *buf, size_t size) {
  static ssize_t (*original)(const char *, char *, size_t);
  if (!original) original = dlsym(RTLD_NEXT, "readlink");
  char self[64];
  snprintf(self, sizeof self, "/proc/%d/exe", (int)getpid());
  return original(strcmp(path, self) == 0 ? "/proc/self/exe" : path, buf, size);
}
