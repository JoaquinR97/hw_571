<<<<<<< HEAD
This repository contains the documentation and starter code for the homework assignments in [CIS 4710/5710: Computer Organization & Design](http://cis.upenn.edu/~cis5710/). Below we describe some of the important computing tools you'll need to use this semester.

# Docker

All of the software tools needed to compile, run and test your code are packaged into the `cis5710/hw-base:latest` Docker container which is [hosted on Docker Hub](https://hub.docker.com/r/cis5710/hw-base). You can install Docker on your computer, and then grab this container to get all of the tools at once. This is the same image that the Gradescope autograder uses as well.

First, install Docker for your OS. For Windows/Mac users, you'll probably want to use [Docker Desktop](https://www.docker.com/get-started/). Linux users may prefer to install via your regular package manager.

Then, you can pull the *container image*, which is the set of files that will be inside the running *container*. Pull the image via:
```
docker pull cis5710/hw-base:latest
```

And then run it to launch the *container*. This puts you inside an Ubuntu Linux command-line system with all of the tools installed. Launch the container with:
```
docker run -it cis5710/hw-base:latest /bin/bash
```

You should also configure Docker to [share a directory with your host machine](https://www.digitalocean.com/community/tutorials/how-to-share-data-between-the-docker-container-and-the-host) so that your files are saved when the container is terminated. We may need to make updates to the container image throughout the semester, so you will want to be able to restart your container (to obtain those updates) without losing your work.

If you'd like to install the tools locally instead, you can follow our [Dockerfile](docker/Dockerfile) for guidance.

# Git
  
We'll use git to distribute the code and instructions for the labs. Here's our recommended git setup so that you can have a private repo you can share with your group partner, and that also allows you to receive updates we make to [the `cis5710-homework` repo](https://github.com/cis5710/cis5710-homework), which we will also refer to as *upstream*. We'll use github in these instructions, but you can adapt these to other hosting situations as well.

> **Do not fork this repo** on GitHub unless you are submitting a Pull Request to fix something here. For doing your homework, you should start from a new private GitHub repo instead (see below).

### Setup an SSH key

Don't type in your password every time you push/pull from your repo. [Setup an SSH key on your github account](https://docs.github.com/en/github/authenticating-to-github/generating-a-new-ssh-key-and-adding-it-to-the-ssh-agent#generating-a-new-ssh-key) to enjoy security _and_ more usability!

### Setup your repo

First, one group member creates a new, empty private repo. **Do not initialize** the repo with a README, a `.gitignore` file, or a license.

Then, run the following commands on the command-line (e.g., on biglab or inside your Docker container). Substitute your GH username and the name of the repo you created for `YOURUSERNAME` and `YOURREPO`, respectively.

First, clone your empty repo (via SSH so that you use the SSH keys you setup previously):
```
git clone git@github.com:YOURUSERNAME/YOURREPO.git
cd YOURREPO
```
Then, add a connection called `upstream` to the upstream CIS 5710 repo and get the changes from `upstream`:
```
git remote add upstream https://github.com/cis5710/cis5710-homework.git
git fetch upstream
```
Now, merge those changes with the `main` branch in your repo:
```
git merge upstream/main
```
Then, push those changes back to your private Github repo:
```
git push
```
Finally, you must initialize the git submodules that this repo uses, with:
```
git submodule update --init --recursive riscv-tests/
```

> You may also have noticed the *solutions* submodule. This is a private repo so you'll get an error if you try to update it, either directly or by trying to update all submodules.

You now have a private repo that is linked with the upstream CIS 5710 repo. Next, [grant your group partner access](https://docs.github.com/en/github/setting-up-and-managing-your-github-user-account/inviting-collaborators-to-a-personal-repository) and then you're ready to go!

### Pulling changes from upstream

To get the latest changes from the upstream CIS 5710 repo, run:
```
git fetch upstream
git merge upstream/main
```

You can also pull in submodule changes via `git submodule update --recursive riscv-tests/`, though that should be only rarely needed.


# VSCode

While you can edit your code however you like, VSCode has decent support for SystemVerilog. I recommend the [Verilog-HDL/SystemVerilog/Bluespec SystemVerilog extension](https://marketplace.visualstudio.com/items?itemName=mshr-h.VerilogHDL) and the Python extension, as those are the languages you'll use most in this class. I also installed [verible](https://github.com/chipsalliance/verible) and enabled `verible-verilog-ls` for code navigation and `verible-verilog-format` for code formatting.

# GtkWave

While most of the tools we use run on the Linux command line, viewing waveforms is best done visually. Thus, you will want to install the GtkWave waveform viewer directly on your machine. In general, waveform files will be generated by running your design inside the container, and then you'll want to view those waveform files *outside* the container. Here's a screenshot of what GtkWave looks like:

![GtkWave screenshot](images/gtkwave-screenshot.png)

### Linux

On Ubuntu:

```
sudo apt-get install gtkwave
```

You can then run `gtkwave SOMETHING.vcd &` to view the waveforms.

### Mac OSX

We recommend you use the [homebrew package manager](https://brew.sh):

```
brew cask install gtkwave
```

Note: If running a new version of homebrew, you may get the following error:
```
Error: `brew cask` is no longer a `brew` command. Use `brew <command> --cask` instead.
```
Change your command to the following: 
```
brew install gtkwave --cask
```

You can then launch `gtkwave`, and open the `.vcd` file with `File => Open New Window` or `File => Open New Tab`. Running `open SOMETHING.vcd` also opens gtkwave automatically, as does double-clicking the `.vcd` file in Finder.

### Windows

Download the Windows version of Gtkwave from [SourceForge](https://sourceforge.net/projects/gtkwave/files/): choose one of the win64 `.zip` files. After you unzip the archive, you can find `gtkwave.exe` inside its `bin` directory, and double-click to launch GtkWave from there. There is no need to install anything.

### General GtkWave tips

The list of signals in the bottom left shows only those for the currently-selected module instance in top-left box. There is also a `filter` box at the bottom you can use to quickly narrow down the list.

**Save your waveform view**

You can use `File => Write Save File` to save a `.gtkw` file that records the signals you have opened, along with radix and color. You can then reload this via `File => Read Save File` when viewing a new waveform to quickly pull up all the useful signals in an organized way.

**Use markers to remember important places**

With `Markers => Drop named marker` you can leave a mark at a particular time to make it easier to find again if you scroll away.
=======
riscv-tests
================

About
-----------

This repository hosts unit tests for RISC-V processors.

Building from repository
-----------------------------

We assume that the RISCV environment variable is set to the RISC-V tools
install path, and that the riscv-gnu-toolchain package is installed.

    $ git clone https://github.com/riscv/riscv-tests
    $ cd riscv-tests
    $ git submodule update --init --recursive
    $ autoconf
    $ ./configure --prefix=$RISCV/target
    $ make
    $ make install

The rest of this document describes the format of test programs for the RISC-V
architecture.

Test Virtual Machines
-------------------------

To allow maximum reuse of a given test, each test program is constrained to
only use features of a given *test virtual machine* or TVM. A TVM hides
differences between alternative implementations by defining:

* The set of registers and instructions that can be used. 
* Which portions of memory can be accessed.
* The way the test program starts and ends execution. 
* The way that test data is input.
* The way that test results are output.

The following table shows the TVMs currently defined for RISC-V. All of these
TVMs only support a single hardware thread.

TVM Name | Description
--- | ---
`rv32ui` | RV32 user-level, integer only
`rv32si` | RV32 supervisor-level, integer only
`rv64ui` | RV64 user-level, integer only
`rv64uf` | RV64 user-level, integer and floating-point
`rv64uv` | RV64 user-level, integer, floating-point, and vector
`rv64si` | RV64 supervisor-level, integer only
`rv64sv` | RV64 supervisor-level, integer and vector

A test program for RISC-V is written within a single assembly language file,
which is passed through the C preprocessor, and all regular assembly
directives can be used. An example test program is shown below. Each test
program should first include the `riscv_test.h` header file, which defines the
macros used by the TVM. The header file will have different contents depending
on the target environment for which the test will be built.  One of the goals
of the various TVMs is to allow the same test program to be compiled and run
on very different target environments yet still produce the same results. The
following table shows the target environment currently defined.

Target Environment Name | Description
--- | ---
`p` | virtual memory is disabled, only core 0 boots up
`pm` | virtual memory is disabled, all cores boot up
`pt` | virtual memory is disabled, timer interrupt fires every 100 cycles
`v` | virtual memory is enabled

Each test program must next specify for which TVM it is designed by including
the appropriate TVM macro, `RVTEST_RV64U` in this example. This specification
can change the way in which subsequent macros are interpreted, and supports
a static check of the TVM functionality used by the program.

The test program will begin execution at the first instruction after
`RVTEST_CODE_BEGIN`, and continue until execution reaches an `RVTEST_PASS`
macro or the `RVTEST_CODE_END` macro, which is implicitly a success. A test
can explicitly fail by invoking the `RVTEST_FAIL` macro.

The example program contains self-checking code to test the result of the add.
However, self-checks rely on correct functioning of the processor instructions
used to implement the self check (e.g., the branch) and so cannot be the only
testing strategy.

All tests should also contain a test data section, delimited by
`RVTEST_DATA_BEGIN` and `RVTEST_DATA_END`. There is no alignment guarantee for
the start of the test data section, so regular assembler alignment
instructions should be used to ensure desired alignment of data values. This
region of memory will be captured at the end of the test to act as a signature
from the test. The signature can be compared with that from a run on the
golden model.

Any given test environment for running tests should also include a timeout
facility, which will class a test as failing if it does not successfully
complete a test within a reasonable time bound.

    #include "riscv_test.h"

    RVTEST_RV64U        # Define TVM used by program.

    # Test code region.
    RVTEST_CODE_BEGIN   # Start of test code.
            lw      x2, testdata
            addi    x2, 1         # Should be 42 into $2.
            sw      x2, result    # Store result into memory overwriting 1s.
            li      x3, 42        # Desired result.
            bne     x2, x3, fail  # Fail out if doesn't match.
            RVTEST_PASS           # Signal success.
    fail:
            RVTEST_FAIL
    RVTEST_CODE_END     # End of test code.

    # Input data section.
    # This section is optional, and this data is NOT saved in the output.
    .data
            .align 3
    testdata:
            .dword 41

    # Output data section.
    RVTEST_DATA_BEGIN   # Start of test output data region.
            .align 3
    result:
            .dword -1
    RVTEST_DATA_END     # End of test output data region.

User-Level TVMs
--------------------

Test programs for the `rv32u*` and `rv64u*` TVMs can contain all instructions
from the respective base user-level ISA (RV32 or RV64), except for those with
the SYSTEM major opcode (syscall, break, rdcycle, rdtime, rdinstret). All user
registers (pc, x0-x31, f0-f31, fsr) can be accessed.

The `rv32ui` and `rv64ui` TVMs are integer-only subsets of `rv32u` and `rv64u`
respectively. These subsets can not use any floating-point instructions (major
opcodes: LOAD-FP, STORE-FP, MADD, MSUB, NMSUB, NMADD, OP-FP), and hence cannot
access the floating-point register state (f0-f31 and fsr). The integer-only
TVMs are useful for initial processor bringup and to test simpler
implementations that lack a hardware FPU.

Note that any `rv32ui` test program is also valid for the `rv32u` TVM, and
similarly `rv64ui` is a strict subset of `rv64u`. To allow a given test to run
on the widest possible set of implementations, it is desirable to write any
given test to run on the smallest or least capable TVM possible. For example,
any simple tests of integer functionality should be written for the `rv64ui`
TVM, as the same test can then be run on RV64 implementations with or without a
hardware FPU. As another example, all tests for these base user-level TVMs will
also be valid for more advanced processors with instruction-set extensions.

At the start of execution, the values of all registers are undefined. All
branch and jump destinations must be to labels within the test code region of
the assembler source file. The code and data sections will be relocated
differently for the various implementations of the test environment, and so
test program results shall not depend on absolute addresses of instructions or
data memory. The test build environment should support randomization of the
section relocation to provide better coverage and to ensure test signatures do
not contain absolute addresses.

Supervisor-Level TVMs
--------------------------

The supervisor-level TVMs allow testing of supervisor-level state and
instructions.  As with the user-level TVMs, we provide integer-only
supervisor-level TVMs indicated with a trailing `i`.

History and Acknowledgements
---------------------------------

This style of test virtual machine originated with the T0 (Torrent-0) vector
microprocessor project at UC Berkeley and ICSI, begun in 1992. The main
developers of this test strategy were Krste Asanovic and David Johnson. A
precursor to `torture` was `rantor` developed by Phil Kohn at ICSI.

A variant of this testing approach was also used for the Scale vector-thread
processor at MIT, begun in 2000. Ronny Krashinsky and Christopher Batten were
the principal architects of the Scale chip. Jeffrey Cohen and Mark Hampton
developed a version of torture capable of generating vector-thread code.
>>>>>>> c2a9b8c72bae1fe6d358cada01eabf39551578ad
