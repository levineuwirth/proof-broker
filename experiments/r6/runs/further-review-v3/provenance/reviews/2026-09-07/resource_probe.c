#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  if (!strcmp(argv[1], "terminal")) {
    const char message[] = "R6_EVENT {\"component\":\"sdk\",\"event\":\"episode_finished\",\"data\":{}}\n";
    return write(2, message, sizeof message - 1) < 0;
  }
  struct timespec start, now;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);
  long target = strtol(argv[1], 0, 10) * 1000000L;
  do {
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &now);
  } while ((now.tv_sec-start.tv_sec)*1000000000L + now.tv_nsec-start.tv_nsec < target);
  return 0;
}
