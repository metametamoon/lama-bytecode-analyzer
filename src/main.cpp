#include "bytefile.h"
#include <algorithm>
#include <cassert>
#include <cstdarg>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <malloc.h>
#include <map>
#include <stdio.h>
#include <string>
#include <unordered_set>
#include <vector>

using u32 = uint32_t;
using i32 = int32_t;
using u8 = std::uint8_t;

#define BOXED(x) (((u32)(x)) & 0x0001)

static i32 constexpr N_GLOBAL = 1000;
static i32 constexpr STACK_SIZE = 100000;

#define DEBUG

#ifdef DEBUG
#define debug(...) fprintf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* Gets a string from a string table by an index */
static inline char const *get_string(bytefile const *f, int pos) {
  // validate its is an ok string
  char *ptr = (char *)&f->stringtab_ptr[pos];
  if (ptr > (char *)f->last_stringtab_zero) {
    fprintf(stderr, "Bad string read at offset %d (string did not terminate)\n",
            pos);
    exit(-1);
  }
  return ptr;
}

/* Gets a name for a public symbol */
static inline char const *get_public_name(bytefile const *f, int i) {
  return get_string(f, f->public_ptr[i * 2]);
}

/* Gets an offset for a publie symbol */
static inline int get_public_offset(bytefile const *f, int i) {
  if (!(i < f->public_symbols_number)) {
    fprintf(stderr, "Trying to read out of bounds public member at %d", i);
    exit(-1);
  }
  return f->public_ptr[i * 2 + 1];
}

enum class BinopLabel {
  ADD = 0,
  SUB = 1,
  MUL = 2,
  DIV = 3,
  MOD = 4,
  LT = 5,
  LEQ = 6,
  GT = 7,
  GEQ = 8,
  EQ = 9,
  NEQ = 10,
  AND = 11,
  OR = 12,
  BINOP_LAST
};

// doing my best to not clah with macros
enum class Patt {
  STR_EQ_TAG = 0,
  STR_TAG = 1,
  ARR_TAG = 2,
  SEXPR_TAG = 3,
  BOXED = 4,
  UNBOXED = 5,
  CLOS_TAG = 6,
  LAST
};

static inline bool check_address(bytefile const *bf, u8 *addr) {
  return (bf->code_ptr <= addr) && (addr < bf->code_end);
}

static inline void print_location(bytefile const *bf, u8 *next_ip) {
  fprintf(stderr, "at 0x%.8x:\n", unsigned((next_ip - 4) - bf->code_ptr - 1));
}

using u8 = std::uint8_t;
static u8 constexpr HBINOP = 0;
static u8 constexpr HMISC1 = 1;
static u8 constexpr HLD = 2;
static u8 constexpr HLDA = 3;
static u8 constexpr HST = 4;
static u8 constexpr HMISC2 = 5;
static u8 constexpr HPATT = 6;
static u8 constexpr HCALL = 7;

enum class HCode : u8 {
  BINOP = 0,
  MISC1 = 1,
  LD = 2,
  LDA = 3,
  ST = 4,
  MISC2 = 5,
  PATT = 6,
  CALL = 7,
  STOP = 15,
};

enum class Misc1LCode : u8 {
  CONST = 0,
  STR = 1,
  SEXP = 2,
  STI = 3,
  STA = 4,
  JMP = 5,
  END = 6,
  RET = 7,
  DROP = 8,
  DUP = 9,
  SWAP = 10,
  ELEM = 11,
};

enum class Misc2LCode : u8 {
  CJMPZ = 0,
  CJMPNZ = 1,
  BEGIN = 2,
  CBEGIN = 3,
  CLOSURE = 4,
  CALLC = 5,
  CALL = 6,
  TAG = 7,
  ARRAY = 8,
  FAILURE = 9,
  LINE = 10,
  ELEM = 11,
};

enum class Call : u8 {
  READ = 0,
  WRITE = 1,
  LLENGTH = 2,
  LSTRING = 3,
  BARRAY = 4,
};

static inline void located_error(bytefile const *bf, u8 *next_ip,
                                 const char *format, ...) {
  fprintf(stderr, "error\n");
  print_location(bf, next_ip);
  va_list argptr;
  va_start(argptr, format);
  vfprintf(stderr, format, argptr);
  fprintf(stderr, "\n");
  exit(-1);
  va_end(argptr);
}

struct DecodeResult {
  std::string command;
  u8 *next_ip; // write after
};

static inline DecodeResult opcode_to_string(u8 *ip, bytefile const *bf) {
  char buff[100];
  i32 offset = 0;
#define FAIL                                                                   \
  {                                                                            \
    printf("ERROR: invalid opcode %d-%d\n", h, l);                             \
    exit(0);                                                                   \
  }

  auto read_int = [&ip, &bf]() {
    check_address(bf, ip);
    ip += sizeof(int);
    return *(int *)(ip - sizeof(int));
  };

  auto read_byte = [&ip, &bf]() {
    check_address(bf, ip);
    return *ip++;
  };

  auto read_string = [&read_int, &ip, &bf]() {
    check_address(bf, ip);
    return get_string(bf, read_int());
  };

  static char const *const ops[] = {
      "+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
  static char const *const pats[] = {"=str", "#string", "#array", "#sexp",
                                     "#ref", "#val",    "#fun"};
  static char const *const lds[] = {"LD", "LDA", "ST"};

  if (ip >= bf->code_end) {
    error("execution unexpectedly got out of code section\n");
  }
  u8 x = read_byte(), h = (x & 0xF0) >> 4, l = x & 0x0F;
  switch ((HCode)h) {
  case HCode::STOP:
    goto stop;

  case HCode::BINOP: {
    offset += sprintf(buff + offset, "BINOP\t%s", ops[l - 1]);
    if (l - 1 < (i32)BinopLabel::BINOP_LAST) {
    } else {
      FAIL;
    }
    break;
  }

  case HCode::MISC1: {
    switch ((Misc1LCode)l) {
    case Misc1LCode::CONST: {
      auto arg = read_int();
      offset += sprintf(buff + offset, "CONST\t%d", arg);
      break;
    }

    case Misc1LCode::STR: {
      char const *string = read_string();
      offset += sprintf(buff + offset, "STRING\t%s", string);
      break;
    }

    case Misc1LCode::SEXP: {
      char const *tag = read_string();
      int n = read_int();
      offset += sprintf(buff + offset, "SEXP\t%s ", tag);
      offset += sprintf(buff + offset, "%d", n);
      break;
    }

    case Misc1LCode::STI: {
      offset += sprintf(buff + offset, "STI");
      break;
    }

    case Misc1LCode::STA: {
      offset += sprintf(buff + offset, "STA");
      break;
    }

    case Misc1LCode::JMP: {
      auto jump_location = read_int();
      offset += sprintf(buff + offset, "JMP\t0x%.8x\n", jump_location);
      break;
    }

    case Misc1LCode::END:
    case Misc1LCode::RET: {
      if (h == 7) {
        offset += sprintf(buff + offset, "RET\n");
      } else {
        offset += sprintf(buff + offset, "END\n");
      }
      break;
    }

    case Misc1LCode::DROP:
      offset += sprintf(buff + offset, "DROP");
      break;

    case Misc1LCode::DUP: {
      offset += sprintf(buff + offset, "DUP");
      break;
    }

    case Misc1LCode::SWAP: {
      offset += sprintf(buff + offset, "SWAP");
      break;
    }

    case Misc1LCode::ELEM: {
      offset += sprintf(buff + offset, "ELEM");
      break;
    }

    default:
      FAIL;
    }
    break;
  }
  case HCode::LD:
  case HCode::LDA:
  case HCode::ST: {
    offset += sprintf(buff + offset, "%s\t", lds[h - 2]);
    i32 const index = read_int();
    switch (l) {
    case 0:
      offset += sprintf(buff + offset, "G(%d)", index);
      break;
    case 1:
      offset += sprintf(buff + offset, "L(%d)", index);
      break;
    case 2:
      offset += sprintf(buff + offset, "A(%d)", index);
      break;
    case 3:
      offset += sprintf(buff + offset, "C(%d)", index);
      break;
    default:
      FAIL;
    }
    break;
  }

  case HCode::MISC2: {
    switch ((Misc2LCode)l) {
    case Misc2LCode::CJMPZ: {
      auto jump_location = read_int();
      offset += sprintf(buff + offset, "CJMPz\t0x%.8x", jump_location);
      break;
    }

    case Misc2LCode::CJMPNZ: {
      auto jump_location = read_int();
      offset += sprintf(buff + offset, "CJMPz\t0x%.8x", jump_location);
      break;
    }

    case Misc2LCode::BEGIN:
    case Misc2LCode::CBEGIN: {
      int n_args = read_int();
      int n_locals = read_int();
      if (l == 3) {
        offset += sprintf(buff + offset, "C");
      }
      offset += sprintf(buff + offset, "BEGIN\t%d ", n_args);
      offset += sprintf(buff + offset, "%d", n_locals);
      break;
    }

    case Misc2LCode::CLOSURE: {
      int addr = read_int();
      offset += sprintf(buff + offset, "CLOSURE\t0x%.8x", addr);
      int n = read_int();
      for (int i = 0; i < n; i++) {
        switch (read_byte()) {
        case 0: {
          int index = read_int();
          offset += sprintf(buff + offset, "G(%d)", index);
          break;
        }
        case 1: {
          int index = read_int();
          offset += sprintf(buff + offset, "L(%d)", index);
          break;
        }
        case 2: {
          int index = read_int();
          offset += sprintf(buff + offset, "A(%d)", index);
          break;
        }
        case 3: {
          int index = read_int();
          offset += sprintf(buff + offset, "C(%d)", index);
          break;
        }
        default:
          FAIL;
        }
      }
      break;
    };

    case Misc2LCode::CALLC: {
      int n_arg = read_int();
      offset += sprintf(buff + offset, "CALLC\t%d", n_arg);
      //  skip closure call
      break;
    }

    case Misc2LCode::CALL: {
      int loc = read_int();
      int n = read_int();
      offset += sprintf(buff + offset, "CALL\t0x%.8x ", loc);
      offset += sprintf(buff + offset, "%d", n);
      break;
    }

    case Misc2LCode::TAG: {
      const char *name = read_string();
      int n = read_int();
      offset += sprintf(buff + offset, "TAG\t%s ", name);
      offset += sprintf(buff + offset, "%d", n);
      break;
    }

    case Misc2LCode::ARRAY: {
      int size = read_int();
      offset += sprintf(buff + offset, "ARRAY\t%d", size);
      break;
    }

    case Misc2LCode::FAILURE:
      offset += sprintf(buff + offset, "FAIL\t%d", read_int());
      offset += sprintf(buff + offset, "%d", read_int());
      // exit(-1); --
      break;

    case Misc2LCode::LINE: {
      int line = read_int();
      offset += sprintf(buff + offset, "LINE\t%d", line);
      break;
    }

    default:
      FAIL;
    }
    break;
  }
  case HCode::PATT: {
    offset += sprintf(buff + offset, "PATT\t%s", pats[l]);
    if (l == 0) { // =str
    } else if (l < (i32)Patt::LAST) {
    } else {
      fprintf(stderr, "Unsupported patt specializer: %d", l);
      FAIL;
    }
    break;
  }
  case HCode::CALL: {
    switch ((Call)l) {
    case Call::READ: {
      offset += sprintf(buff + offset, "CALL\tLread");
      break;
    }

    case Call::WRITE: {
      offset += sprintf(buff + offset, "CALL\tLwrite");
      break;
    }
    case Call::LLENGTH: {
      offset += sprintf(buff + offset, "CALL\tLlength");
      break;
    }

    case Call::LSTRING: {
      offset += sprintf(buff + offset, "CALL\tLstring");
      break;
    }

    case Call::BARRAY: {
      i32 n = read_int();
      offset += sprintf(buff + offset, "CALL\tBarray\t%d", n);
      break;
    }

    default:
      FAIL;
    }
  } break;

  default:
    FAIL;
  }
  return DecodeResult{std::string{buff}, ip};
stop:
  debug(stderr, "<end>\n");
  return DecodeResult{std::string{"<end>\n"}, ip};
}

// by convention if no jump might be possible, it is in next_ip
// if jump is possible, it is in alternative_next_ip
struct InstructionResult {
  u8 *next_ip;
  u8 *alternative_next_ip;
};

static inline InstructionResult run_instruction(u8 *ip, bytefile const *bf,
                                                bool print_inst) {
#define FAIL                                                                   \
  {                                                                            \
    printf("ERROR: invalid opcode %d-%d\n", h, l);                             \
    exit(0);                                                                   \
  }

  auto read_int = [&ip, &bf]() {
    check_address(bf, ip);
    ip += sizeof(int);
    return *(int *)(ip - sizeof(int));
  };

  auto read_byte = [&ip, &bf]() {
    check_address(bf, ip);
    return *ip++;
  };

  auto read_string = [&read_int, &ip, &bf]() {
    check_address(bf, ip);
    return get_string(bf, read_int());
  };

  static char const *const ops[] = {
      "+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
  static char const *const pats[] = {"=str", "#string", "#array", "#sexp",
                                     "#ref", "#val",    "#fun"};
  static char const *const lds[] = {"LD", "LDA", "ST"};
  // bool in_closure = false;
  auto check_is_begin = [](bytefile const *bf, u8 *ip) {
    if (!check_address(bf, ip)) {
      return false;
    }
    u8 x = *ip;
    u8 h = (x & 0xF0) >> 4, l = x & 0x0F;
    return h == 5 && (l == 3 || l == 2);
  };

  do {
    if (ip >= bf->code_end) {
      error("execution unexpectedly got out of code section\n");
    }
    if (print_inst) {
      fprintf(stderr, "0x%.8x:\t", unsigned(ip - bf->code_ptr));
      auto result = opcode_to_string(ip, bf);
      fprintf(stderr, "%s\n", result.command.c_str());
    }

    u8 x = read_byte(), h = (x & 0xF0) >> 4, l = x & 0x0F;

    switch ((HCode)h) {
    case HCode::STOP:
      goto stop;

    case HCode::BINOP: {
      if (l - 1 < (i32)BinopLabel::BINOP_LAST) {
      } else {
        FAIL;
      }
      break;
    }

    case HCode::MISC1: {
      switch ((Misc1LCode)l) {
      case Misc1LCode::CONST: {
        auto arg = read_int();
        break;
      }

      case Misc1LCode::STR: {
        char const *string = read_string();
        break;
      }

      case Misc1LCode::SEXP: {
        char const *tag = read_string();
        int n = read_int();
        break;
      }

      case Misc1LCode::STI: {
        break;
      }

      case Misc1LCode::STA: {
        break;
      }

      case Misc1LCode::JMP: {
        auto jump_location = read_int();
        u8 *old_ip = ip;
        u8 *jump_ip = bf->code_ptr + jump_location;
        if (!check_address(bf, jump_ip)) {
          print_location(bf, old_ip);
          fprintf(stderr, "trying to jump out of the code area to offset %d",
                  jump_ip - bf->code_ptr);
        }
        return InstructionResult{nullptr, jump_ip};
        break;
      }

      case Misc1LCode::END:
      case Misc1LCode::RET: {
        if (h == 7) {
        } else {
        }
        return InstructionResult{
            nullptr,
            nullptr,
        };
        break;
      }

      case Misc1LCode::DROP:
        break;

      case Misc1LCode::DUP: {
        break;
      }

      case Misc1LCode::SWAP: {
        break;
      }

      case Misc1LCode::ELEM: {
        break;
      }

      default:
        FAIL;
      }
      break;
    }
    case HCode::LD:
    case HCode::LDA:
    case HCode::ST: {
      i32 const index = read_int();
      switch (l) {
      case 0:
        break;
      case 1:
        break;
      case 2:
        break;
      case 3:
        break;
      default:
        FAIL;
      }
      break;
    }

    case HCode::MISC2: {
      switch ((Misc2LCode)l) {
      case Misc2LCode::CJMPZ: {
        auto jump_location = read_int();
        auto possible_next = ip;
        auto result = InstructionResult{
            possible_next,
            nullptr,
        };
        u8 *jump_ip = bf->code_ptr + jump_location;
        if (!check_address(bf, jump_ip)) {
          print_location(bf, ip);
          fprintf(stderr, "trying to jump out of the code area to offset %d",
                  jump_ip - bf->code_ptr);
        }
        result.alternative_next_ip = jump_ip;
        return result;
        break;
      }

      case Misc2LCode::CJMPNZ: {
        auto jump_location = read_int();
        auto possible_next = ip;
        auto result = InstructionResult{
            possible_next,
            nullptr,
        };
        u8 *jump_ip = bf->code_ptr + jump_location;
        if (!check_address(bf, jump_ip)) {
          print_location(bf, ip);
          fprintf(stderr, "trying to jump out of the code area to offset %d",
                  jump_ip - bf->code_ptr);
        }
        result.alternative_next_ip = jump_ip;
        return result;
        break;
      }

      case Misc2LCode::BEGIN:
      case Misc2LCode::CBEGIN: {
        int n_args = read_int();
        int n_locals = read_int();
        if (l == 3) {
        }
        break;
      }

      case Misc2LCode::CLOSURE: {
        int addr = read_int();
        if (addr < 0 || addr > (bf->code_end - bf->code_ptr)) {
          located_error(bf, ip, "closure points outside of the code area\n");
        }
        if (!check_is_begin(bf, bf->code_ptr + addr)) {
          located_error(bf, ip, "closure does not point at begin\n");
        }
        int n = read_int();
        for (int i = 0; i < n; i++) {
          switch (read_byte()) {
          case 0: {
            int index = read_int();
            break;
          }
          case 1: {
            int index = read_int();
            break;
          }
          case 2: {
            int index = read_int();
            break;
          }
          case 3: {
            int index = read_int();
            break;
          }
          default:
            FAIL;
          }
        }
        break;
      };

      case Misc2LCode::CALLC: {
        int n_arg = read_int();
        //  skip closure call
        break;
      }

      case Misc2LCode::CALL: {
        int loc = read_int();
        int n = read_int();
        auto called_function_begin = bf->code_ptr + loc;
        if (!check_is_begin(bf, called_function_begin)) {
          located_error(bf, ip, "CALL does not call a function\n");
          ;
        }
        return InstructionResult{
            ip,
            called_function_begin,
        };
        break;
      }

      case Misc2LCode::TAG: {
        const char *name = read_string();
        int n = read_int();
        break;
      }

      case Misc2LCode::ARRAY: {
        int size = read_int();
        break;
      }

      case Misc2LCode::FAILURE: {
        return InstructionResult{
            nullptr,
            nullptr,
        };
        break;
      }

      case Misc2LCode::LINE: {
        int line = read_int();
        break;
      }

      default:
        FAIL;
      }
      break;
    }
    case HCode::PATT: {
      if (l == 0) { // =str
      } else if (l < (i32)Patt::LAST) {
      } else {
        fprintf(stderr, "Unsupported patt specializer: %d", l);
        FAIL;
      }
      break;
    }
    case HCode::CALL: {
      switch ((Call)l) {
      case Call::READ: {
        break;
      }

      case Call::WRITE: {
        break;
      }
      case Call::LLENGTH: {
        break;
      }

      case Call::LSTRING: {
        break;
      }

      case Call::BARRAY: {
        i32 n = read_int();
        break;
      }

      default:
        FAIL;
      }
    } break;

    default:
      FAIL;
    }

    return InstructionResult{ip, nullptr};
  } while (1);
stop:
  debug(stderr, "<end>\n");
  return InstructionResult{nullptr, nullptr};
}

/* Dumps the contents of the file */
static inline void dump_file(FILE *f, bytefile const *bf) {
  int i;

  debug(stderr, "String table size       : %d\n", bf->stringtab_size);
  debug(stderr, "Global area size        : %d\n", bf->global_area_size);
  debug(stderr, "Number of public symbols: %d\n", bf->public_symbols_number);
  debug(stderr, "Public symbols          :\n");

  for (i = 0; i < bf->public_symbols_number; i++)
    debug(stderr, "   0x%.8x: %s\n", get_public_offset(bf, i),
          get_public_name(bf, i));

  debug(stderr, "Code:\n");
  run_instruction(bf->code_ptr, bf, true);
}

struct InstructionBlock {
  u8 *begin;
  u8 size_bytes;
};

struct InstructionBlockCompare {
  bool operator()(InstructionBlock const &left,
                  InstructionBlock const &right) const {
    if (left.size_bytes != right.size_bytes) {
      return left.size_bytes < right.size_bytes;
    }
    for (u8 i = 0; i < left.size_bytes; ++i) {
      if (left.begin[i] != right.begin[i]) {
        return left.begin[i] < right.begin[i];
      }
    }
    return false; // equal
  }
};

void account_instruction_blocks(
    i32 inst_per_block, std::vector<std::pair<InstructionBlock, i32>> &out,
    bytefile const *bf) {
  std::map<InstructionBlock, i32, InstructionBlockCompare> counter;
  std::vector<u8 *> dfs_queue;
  std::unordered_set<u8 *> visited; // was at some point put in the dfs_queue
  dfs_queue.push_back(bf->code_ptr);
  auto push_if_not_visited = [&visited, &dfs_queue, &bf](u8 *possible_ip) {
    if (visited.count(possible_ip) == 0) {
      dfs_queue.push_back(possible_ip);
      visited.insert(possible_ip);
      // fprintf(stderr, "enqueued %x\n", possible_ip - bf->code_ptr);
    }
  };

  while (!dfs_queue.empty()) {
    u8 *ip = dfs_queue.back();
    dfs_queue.pop_back();

    auto const result = run_instruction(ip, bf, false);
    if (result.alternative_next_ip != nullptr) {
      push_if_not_visited(result.alternative_next_ip);
    }
    if (result.next_ip != nullptr) {
      push_if_not_visited(result.next_ip);
    }
    if (result.next_ip != nullptr) {
      u8 *read_ip = result.next_ip;
      bool success = true;
      for (i32 i = 0; i < inst_per_block - 1; ++i) {
        auto subResult = run_instruction(read_ip, bf, false);
        if (subResult.alternative_next_ip != nullptr ||
            subResult.next_ip == nullptr) {
          success = false;
          break;
        }
        read_ip = subResult.next_ip;
      }
      if (success) {
        InstructionBlock block = InstructionBlock{ip, (u8)(read_ip - ip)};
        counter[block] += 1;
      }
    }
  }
  for (auto [key, value] : counter) {
    // run_instruction(key->begin, bf);
    out.push_back({key, value});
  }
}

void print_results(std::vector<std::pair<InstructionBlock, i32>>& sorted_result, bytefile const *bf) {
  for (auto [instr, occurences] : sorted_result) {
    std::string total_str;
    u8 *inp = instr.begin;
    while (inp != instr.begin + instr.size_bytes) {
      auto decoded = opcode_to_string(inp, bf);
      inp = decoded.next_ip;
      total_str += decoded.command;
      total_str += ";";
    }
    printf("cnt=%d: %s\n", occurences, total_str.c_str());
  }
}

int main(int argc, char *argv[]) {
  bytefile const *bf = read_file(argv[1]);
  std::vector<std::pair<InstructionBlock, i32>> result;
  account_instruction_blocks(1, result, bf);
  account_instruction_blocks(2, result, bf);
  std::sort(result.begin(), result.end(),
            [](std::pair<InstructionBlock, i32> const &x,
               std::pair<InstructionBlock, i32> const &y) {
              return x.second > y.second;
            });
  print_results(result, bf);
  
  return 0;
}