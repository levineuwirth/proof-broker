/* Adversarial subprocess trees for the external budget supervisor. */
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  if (!strcmp(argv[1], "output")) {
    char buf[8192]; memset(buf, 'x', sizeof buf);
    for (;;) if (write(1, buf, sizeof buf) < 0) return 1;
  }
  for (int i = 0; i < 4; ++i) {
    pid_t child = fork();
    if (child < 0) return 2;
    if (child == 0) {
      /* A new process group must still count against the cgroup budget. */
      setsid();
      if (!strcmp(argv[1], "memory")) {
        size_t n = 96 * 1024 * 1024;
        volatile char *p = malloc(n);
        if (!p) return 3;
        for (size_t j = 0; j < n; j += 4096) p[j] = 1;
        for (;;) pause();
      }
      if (!strcmp(argv[1], "wall")) for (;;) pause();
      volatile unsigned long n = 0;
      for (;;) ++n;
    }
  }
  while (wait(NULL) > 0) {}
  return 1;
}
