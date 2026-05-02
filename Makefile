CRANE_DIR := crane
SDL2_BINDINGS_DIR := rocq-crane-sdl2
BUILD_DIR := _build/RocqsweeperGame
SRC_DIR   := src
GEN_DIR   := $(SRC_DIR)/generated
WEB_DIR   := docs
WEB_BUILD_DIR := _build/web
WEB_SHELL := $(SRC_DIR)/web_shell.html
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
  else
    CXX := /usr/bin/clang++
  endif
endif

IS_CLANG := $(shell $(CXX) --version 2>/dev/null | grep -qi clang && echo yes)
BRACKET_DEPTH_FLAG :=
ifeq ($(IS_CLANG),yes)
  BRACKET_DEPTH_FLAG := -fbracket-depth=1024
endif

SDL2_CFLAGS = $(shell pkg-config --cflags sdl2 SDL2_image SDL2_mixer)
SDL2_LIBS   = $(shell pkg-config --libs sdl2 SDL2_image SDL2_mixer)

CXXFLAGS = -std=c++23 $(BRACKET_DEPTH_FLAG) -I$(GEN_DIR) -I$(SDL2_BINDINGS_DIR)/src -I$(CRANE_DIR)/theories/cpp $(SDL2_CFLAGS)
EMXX ?= em++
WEB_PORT_FLAGS = -sUSE_SDL=2 -sUSE_SDL_IMAGE=2 -sUSE_SDL_MIXER=2 -sSDL2_MIXER_FORMATS='["mp3"]'
WEB_CXXFLAGS = -std=c++23 -fbracket-depth=1024 -I$(GEN_DIR) -I$(SDL2_BINDINGS_DIR)/src -I$(CRANE_DIR)/theories/cpp $(WEB_PORT_FLAGS)
WEB_LDFLAGS = $(WEB_PORT_FLAGS) -sALLOW_MEMORY_GROWTH=1 -sNO_EXIT_RUNTIME=1 --preload-file assets --shell-file $(WEB_SHELL)
OPT ?= -O2

.PHONY: all clean run extract check check-crane check-sdl-bindings install-crane install-sdl-bindings web

all: rocqsweeper

check-crane:
	@test -d $(CRANE_DIR)/theories/cpp || \
	  (echo "error: Crane not found at ./$(CRANE_DIR)"; \
	   echo "expected symlink or checkout matching ~/work/rocqman/crane"; \
	   exit 1)

check-sdl-bindings:
	@test -d $(SDL2_BINDINGS_DIR)/theories || \
	  (echo "error: SDL2 bindings not found at ./$(SDL2_BINDINGS_DIR)"; \
	   echo "Run: git submodule update --init"; \
	   exit 1)

install-crane: check-crane
	cd $(CRANE_DIR) && dune build -p rocq-crane @install && dune install -p rocq-crane

install-sdl-bindings: install-crane check-sdl-bindings
	cd $(SDL2_BINDINGS_DIR) && dune build -p rocq-crane-sdl2 @install && dune install -p rocq-crane-sdl2

extract: check-crane check-sdl-bindings install-sdl-bindings theories/Rocqsweeper.v
	dune clean
	dune build theories/Rocqsweeper.vo
	@mkdir -p $(GEN_DIR)
	cp $(BUILD_DIR)/rocqsweeper.h $(BUILD_DIR)/rocqsweeper.cpp $(GEN_DIR)/

check:
	$(MAKE) install-sdl-bindings
	dune build -p rocqsweeper

$(GEN_DIR)/rocqsweeper.cpp $(GEN_DIR)/rocqsweeper.h: theories/Rocqsweeper.v
	$(MAKE) extract

rocqsweeper: check-crane $(GEN_DIR)/rocqsweeper.cpp $(GEN_DIR)/rocqsweeper.h
	$(CXX) $(CXXFLAGS) $(OPT) $(LDFLAGS) $(GEN_DIR)/rocqsweeper.cpp $(SDL2_LIBS) -o rocqsweeper

web: check-crane $(GEN_DIR)/rocqsweeper.cpp $(GEN_DIR)/rocqsweeper.h src/web_main.cpp $(WEB_SHELL)
	@mkdir -p $(WEB_DIR)
	@mkdir -p $(WEB_BUILD_DIR)
	rm -f $(WEB_DIR)/rocqsweeper.* $(WEB_DIR)/index.html $(WEB_DIR)/index.js $(WEB_DIR)/index.wasm $(WEB_DIR)/index.data
	$(EMXX) $(WEB_CXXFLAGS) $(OPT) -Dmain=rocqsweeper_generated_main -c $(GEN_DIR)/rocqsweeper.cpp -o $(WEB_BUILD_DIR)/rocqsweeper.o
	$(EMXX) $(WEB_CXXFLAGS) $(OPT) -c src/web_main.cpp -o $(WEB_BUILD_DIR)/web_main.o
	$(EMXX) $(WEB_BUILD_DIR)/rocqsweeper.o $(WEB_BUILD_DIR)/web_main.o $(WEB_LDFLAGS) -o $(WEB_DIR)/index.html

clean:
	dune clean
	rm -rf rocqsweeper $(GEN_DIR) rocqsweeper.dSYM $(WEB_DIR) $(WEB_BUILD_DIR)

run: rocqsweeper
	./rocqsweeper
