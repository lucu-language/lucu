

> [!WARNING]  
> This language is still highly unstable and can have changes made to syntax on a whim. Please wait for the first release for stability.

# lucu

A systems language with its key feature being _lexical effect handlers_.

```coffeescript
import "core:io"

fun main() / io.stdio {
	io.putstr("Hello, World!")
}
```

## Usage

The project currently only supports Linux. Cross-compilation to windows is functional, but compilation on windows itself is untested. There is no compilation target for MacOS yet.

This is a cargo rust project, so you need cargo installed with the latest stable rust compiler. Furthermore, you need `llvm-15` installed. Many distributions will have a package for this. Note that the lucu compiler specifically depends on version _15_ of LLVM. Then it's as easy as running `cargo build --release`. The executable will be inside the `target/release` folder.

Note that the executable will have the `core/` and `vendor/` folders inside the sources hardcoded as the location for the standard library. To change this, set the `LUCU_CORE` environment variable to the folder containing these two folders before compiling the compiler.

The compiler will automatically attempt run the output file. In future this will be a flag.

### Linux

Dependencies

- `ld`

For compilatation on linux, run

- `lucu [FILE] (--output [OUTPUT])`

### Windows (cross-compilation)

Dependencies

- `x86_64-w64-mingw32-ld`

For compiling to Windows from linux, run

- `lucu [FILE] (--output [OUTPUT]) --target x86_64-mingw32`

### WASM standalone (cross-compilation)

Dependencies

- `wasm-ld`

For compiling to WASM from linux, run

- `lucu [FILE] (--output [OUTPUT]) --target wasm32` or `wasm64`

### WASI (cross-compilation)

Dependencies

- `wasm-ld`
- `wasmtime`

For compiling to WASI from linux, run

- `lucu [FILE] (--output [OUTPUT]) --target wasm32-wasi`

## Effects?

Lucu has a notion of effects and handlers. These are similar to effects found in the `koka` or `effekt` programming languages.

Succinctly, effects are an interface of available functions whose instances (handlers) are lexically bound to a scope.

What does that mean?

### Effects as capabilities

Some parts of a codebase should have access to graphics libraries, while others should not. Some should access the file system, and others should be far away from filesystem logic. Effects provide a standard set of functions, and to use those functions an effect needs to be on the "effect stack" of a function. This way the developer can color their functions based on what capabilities it has. If a function does not have the `fs` effect on its stack, then it will never be able to interact with the console.

Example of a definition of `fs`:

```coffeescript
effect fs {
  fun exists(s str) bool
  fun mkdir(s str)
  fun parent(s str) str
  # ...
}

fun make_recursive_dir(s str) / fs {
  # this function has "fs" in its stack
  # this means it can use the functions defined within
  if !exists(s) {
    make_recursive_dir(parent(s))
    mkdir(s)
  }
}

fun successor(i int) int {
  # this function has no effects mentioned in its stack
  # this means the function _must_ be pure, and its output is solely based on its input
  i + 1
}
```

Of course, this example does not include defining a handler for `fs`. An effect like that is most likely defined using OS-specific syscalls or kernel library calls. Here is an example for defining an `io.writer` that writes to an array:

```coffeescript
# inside core/io/write.lucu
effect writer {
  fun write(bytes []u8) usize
  fun flush()
}

# inside examples/write_buffer.lucu (try it yourself!)
import "core:io"

fun main() / io.stdio {
  # set a 1024 length buffer to 0
  mut buf [1024]u8 = 0

  # define a handler for writing to the buffer
  mut ptr usize = 0
  let handler = handle io.writer {
    fun write(bytes []u8) usize {
      mut written usize = 0
      while() { and(ptr < 1024, written < len(bytes)) } {
        buf[ptr++] = bytes[written++]
      }
      written
    }
    fun flush() {}
  }

  # use handler
  with handler {
    io.write("Hello")
    io.write(", ")
    io.write("World")
    io.write("!\n")
  }

  # print the entire buffer to the console
  io.write(buf[0 .. ptr]) with io.stdout();
}
```

### Effects as typeclasses

Let's say an effect handler is bound to the global scope, so it is always available. This is then similar to Haskell typeclasses. It is also similar to Java interfaces or Rust traits, but these are required to be defined for a specific type. Lucu effects can contain type generics, but they can also be independent. Globally defined handlers may be used even if a function does not have the effect in its effect stack.

Here is an example of an effect with global handlers for writing datatypes to a (string) writer:

```coffeescript
effect show(`t) {
  fun show(t `t) / io.writer
}

handle show(int) {
  fun show(i int) / io.writer {
    io.write_int(i)
  }
}

handle show(str) {
  fun show(s str) / io.writer {
    io.write(cast s)
  }
}
```

> [!WARNING]  
> Generics in lucu effects are not fully supported yet and will crash the compiler. It is being worked on

### Effects for typed exceptions

TODO (see https://github.com/Astavie/lucu/blob/main/examples/div.lucu)

## Examples

- Good amount of comments:
  - https://github.com/Astavie/lucu/blob/main/examples/iter.lucu
  - https://github.com/Astavie/lucu/blob/main/examples/div.lucu
- Fun projects to look at:
  - https://github.com/Astavie/lucu/blob/main/examples/brainfuck.lucu
  - https://github.com/Astavie/lucu/blob/main/examples/conway.lucu
