/* R6-001 fixture transport. It sees only a request and its selected witness.
   It performs no proof search and executes no model-generated source. */
#include <stdio.h>
#include <string.h>
#include <unistd.h>

int main(int argc, char **argv) {
  if (argc != 3) return 2;
  FILE *request = fopen("/request.json", "rb");
  if (!request) return 3;
  int ch, count = 0;
  while ((ch = fgetc(request)) != EOF) ++count;
  fclose(request);
  if (count == 0) return 4;
  if (!strcmp(argv[1], "timeout")) { for (;;) pause(); }
  if (!strcmp(argv[1], "malformed")) { puts("{\"witness\":"); return 0; }
  FILE *witness = fopen("/witness.json", "rb");
  if (!witness) return 5;
  printf("{\"request_sha256\":\"%s\",\"witness\":", argv[2]);
  while ((ch = fgetc(witness)) != EOF) putchar(ch);
  fclose(witness);
  puts("}");
  return 0;
}
