CRANE_DIR := crane
BUILD_DIR := _build/RocqsweeperGame
SRC_DIR   := src
GEN_DIR   := $(SRC_DIR)/generated
UNAME_S := $(shell uname -s)

ifeq ($(origin CXX), default)
  CXX := c++
endif
LDFLAGS :=

ifeq ($(UNAME_S),Darwin)
  BREW_LLVM := $(shell brew --prefix llvm 2>/dev/null)
  BREW_CLANG := $(BREW_LLVM)/bin/clang++
  ifneq ($(wildcard $(BREW_CLANG)),)
    CXX := $(BREW_CLANG)
    LDFLAGS := -L$(BREW_LLVM)/lib/c++ -Wl,-rpath,$(BREW_LLVM)/lib/c++
  endif
endif

IS_CLANG := $(shell $(CXX) --version 2>/dev/null | grep -qi clang && echo yes)
BRACKET_DEPTH_FLAG :=
ifeq ($(IS_CLANG),yes)
  BRACKET_DEPTH_FLAG := -fbracket-depth=1024
endif

SDL2_CFLAGS := $(shell pkg-config --cflags sdl2 SDL2_image)
SDL2_LIBS   := $(shell pkg-config --libs sdl2 SDL2_image)

CXXFLAGS := -std=c++23 $(BRACKET_DEPTH_FLAG) -I$(GEN_DIR) -I$(SRC_DIR) -I$(CRANE_DIR)/theories/cpp $(SDL2_CFLAGS)
OPT ?= -O0

.PHONY: all clean run extract check-crane repro

all: rocqsweeper

check-crane:
	@test -d $(CRANE_DIR)/theories/cpp || \
	  (echo "error: Crane not found at ./$(CRANE_DIR)"; \
	   echo "expected symlink or checkout matching ~/work/rocqman/crane"; \
	   exit 1)

extract: check-crane theories/Rocqsweeper.v theories/SDL.v
	dune clean
	dune build theories/Rocqsweeper.vo
	@mkdir -p $(GEN_DIR)
	cp $(BUILD_DIR)/rocqsweeper.h $(BUILD_DIR)/rocqsweeper.cpp $(GEN_DIR)/

$(GEN_DIR)/rocqsweeper.cpp $(GEN_DIR)/rocqsweeper.h: theories/Rocqsweeper.v theories/SDL.v
	$(MAKE) extract

rocqsweeper: check-crane $(GEN_DIR)/rocqsweeper.cpp $(GEN_DIR)/rocqsweeper.h
	$(CXX) $(CXXFLAGS) $(OPT) $(LDFLAGS) $(SDL2_LIBS) $(GEN_DIR)/rocqsweeper.cpp -o rocqsweeper

clean:
	dune clean
	rm -rf rocqsweeper $(GEN_DIR) rocqsweeper.dSYM

run: rocqsweeper
	./rocqsweeper

repro: check-crane theories/CraneMoveSharedPtrSegfault.v
	dune clean
	dune build theories/CraneMoveSharedPtrSegfault.vo
	$(CXX) -std=c++23 -I$(BUILD_DIR) -I$(CRANE_DIR)/theories/cpp -include iostream -include string \
		$(BUILD_DIR)/crane_move_shared_ptr_segfault.cpp \
		-o crane_move_shared_ptr_segfault
