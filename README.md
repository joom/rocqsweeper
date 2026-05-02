# Rocqsweeper

Rocqsweeper is a Minesweeper game written in Rocq and extracted to C++ with [Crane](https://github.com/bloomberg/crane). The game uses the separate [rocq-crane-sdl2](https://github.com/joom/rocq-crane-sdl2) bindings package for SDL2 rendering, input, textures, and audio.

![Rocqsweeper screenshot](assets/screenshot.png)

## Features

- game logic written in Rocq
- extraction to C++ with Crane
- SDL2 rendering
- keyboard and mouse controls
- sound effects for revealing a mine, revealing a safe cell, and winning
- machine-checked proofs about the core game logic and the input layer

## Requirements

You need:

- Rocq with `dune`
- a C++23 compiler
- `pkg-config`
- SDL2
- SDL2_image
- SDL2_mixer
- Emscripten, if you want the WebAssembly build

## Getting started

Clone the repo with everything it needs:

```bash
git clone --recurse-submodules https://github.com/joom/rocqsweeper.git
cd rocqsweeper
```

If you already cloned it without submodules, run:

```bash
git submodule update --init --recursive
```

## Installing dependencies

### macOS

Install the SDL packages with Homebrew:

```bash
brew install sdl2 sdl2_image sdl2_mixer
```

If you want to use Homebrew LLVM instead of the system toolchain:

```bash
brew install llvm
```

### Linux

The exact package names vary by distribution, but you generally need:

```bash
sudo apt install clang pkg-config libsdl2-dev libsdl2-image-dev libsdl2-mixer-dev
```

### opam

If you want to build the Rocq development through opam, pin the local Crane
and SDL2 binding submodules first:

```bash
opam pin add rocq-crane ./crane
opam pin add rocq-crane-sdl2 ./rocq-crane-sdl2
```

Then you can install the Rocqsweeper package from the current checkout:

```bash
opam install .
```

## Building

Build the game:

```bash
make
```

This does four things:

1. uses the local Crane checkout in `./crane`
2. uses the local SDL2 binding checkout in `./rocq-crane-sdl2`
3. extracts [`theories/Rocqsweeper.v`](./theories/Rocqsweeper.v) to C++
4. copies the generated C++ into `src/generated/`
5. compiles the final executable `./rocqsweeper`

Build with a different optimization level:

```bash
make OPT=-O2
```

Run only the extraction step:

```bash
make extract
```

Run the Dune package check:

```bash
make check
```

## WebAssembly Build

The generated C++ can also be compiled with Emscripten:

```bash
make web
```

This builds:

```text
docs/index.html
docs/index.js
docs/index.wasm
docs/index.data
```

The web target uses Emscripten's SDL2 ports and preloads `assets/`, so the
sound effects remain available through the virtual filesystem. It also uses a
small browser-specific entry point in [`src/web_main.cpp`](./src/web_main.cpp)
so the game advances one frame at a time through `emscripten_set_main_loop_arg`
instead of running the native recursive `main` loop.

Serve the generated files from a local HTTP server:

```bash
python3 -m http.server 8000 -d docs
```

Then open:

```text
http://localhost:8000/
```

## Running

Run the game:

```bash
make run
```

or:

```bash
./rocqsweeper
```

Controls:

- arrow keys or `WASD`: move cursor
- `Space`: reveal cell
- `F`: toggle flag
- left click: reveal cell
- right click: toggle flag
- `R`: restart
- `Q` or `Esc`: quit

## Cleaning

Remove build outputs:

```bash
make clean
```

This removes:

- `./rocqsweeper`
- `./src/generated/`
- `./rocqsweeper.dSYM`
- `./docs/`
- Dune build outputs

## Repository structure

```text
.
├── assets/
│   └── *.mp3                sound effects
├── crane/                   Crane submodule used for extraction
├── rocq-crane-sdl2/         SDL2 binding submodule used by the game
├── src/
│   ├── generated/           extracted C++ build artifacts
│   ├── web_main.cpp         browser main loop entry point
│   └── web_shell.html       Emscripten HTML shell
├── theories/
│   ├── GameProofs.v         proofs about the core Minesweeper rules
│   ├── InteractionProofs.v  proofs about cursor movement and event handling
│   ├── Rocqsweeper.v        game logic, rendering, sounds, extracted main loop
│   └── dune                 Rocq theory stanza
├── Makefile                 extraction and native build entrypoint
├── dune-project             Dune project file
└── README.md
```

Generated files are written to:

```text
src/generated/
```

These are build artifacts and should not be edited manually.

## What Is Proved

The files [`theories/GameProofs.v`](./theories/GameProofs.v) and [`theories/InteractionProofs.v`](./theories/InteractionProofs.v) contain machine-checked proofs about the current game logic. At the moment, those proofs show that restarting returns the game to a clean blank board, first-click mine generation keeps the chosen starting cell safe, toggling a flag preserves mine placement and adjacency counts, the reveal flood-fill core preserves mine placement and does not increase the number of hidden safe cells, and pure gameplay traces preserve the main well-formedness and outcome invariants. They also prove that cursor updates stay within bounds, mouse actions outside the board are no-ops, mouse actions inside the board map to the expected reveal and flag operations, and restart and quit events are interpreted correctly by the event handler.

These proofs are about the actual Rocq implementation in [`theories/Rocqsweeper.v`](./theories/Rocqsweeper.v), not a separate paper model. They do not attempt to verify SDL itself or the extracted C++ runtime.

## Development notes

- The authoritative game logic lives in Rocq, not in the generated C++.
- The build expects Crane at [`crane/`](./crane).
- The build also expects the SDL2 bindings at [`rocq-crane-sdl2/`](./rocq-crane-sdl2).
- The opam package expects you to pin both local submodules manually with `opam pin add rocq-crane ./crane` and `opam pin add rocq-crane-sdl2 ./rocq-crane-sdl2`.
- [`rocq-crane-sdl2/src/sdl_helpers.h`](./rocq-crane-sdl2/src/sdl_helpers.h) is the handwritten C++ SDL integration layer used by extraction.
- The extracted program now defines its own `main`, so there is no separate handwritten `main.cpp`.
- [`rocq-crane-sdl2/src/sdl_helpers.h`](./rocq-crane-sdl2/src/sdl_helpers.h) initializes SDL audio lazily and caches loaded sound chunks for reuse.
