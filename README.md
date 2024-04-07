# lh-tactics-test

Replication package for Daniel's undergraduate thesis, building on the _[Liquid Proof Macros][liquid-proof-macros]_ paper.

## Documentation

See the paper _[Liquid Proof Macros][liquid-proof-macros]_ and
the examples in `props-done/` for details on how to use `lh-tactics`.

## Installation
Clone this repo, then run `cd lh-tactics-test/; git submodule update --init` in the terminal.

### Recommended Approach (Using Docker + VSCode)
Install the [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) extension in VSCode. When promped to 'Open in Container', choose this option. The installation takes quite long (~45 mins to install all the dependencies).

### Manual Approach (Not recommended)
This approach is not recommended since you may run into dependency issues when trying to perform the manual installation. To install manually, 
```sh
cp lh-tactics.cabal-correct /workspaces/lh-tactics-test/lh-tactics/lh-tactics.cabal
cd lh-tactics-test/lh-tactics
stack build; stack install
```

## Running one of our tests

The following example shows how to run the `lh-tactics` tool on one of the
examples included in the set of examples used in the evaluation mentioned in
_[Liquid Proof Macros][liquid-proof-macros]_ Inside `lh-tactics-test/`, run the
following commands:

```sh
# copy the file that contains the example into `src/TIP/`
cp props-done/Prop1.hs src/TIP/

# run the `lh-tactics` tool on `Prop1`
stack clean
lh-tactics src/TIP/Prop1.hs:prop1_proof
```
This will output some debugging and logging information, and modify the file
`src/TIP/Prop1.hs` in place. Give it a few seconds to complete (it will give you
feedback as it runs). You can have the file open in a modern text editor such as
VSCode in order to watch the proof term being generated.

**IMPORTANT**: Building `lh-tactics-test` straightforwardly with `stack build`
will not run `liquid-haskell` (you can see it is commented out in
`package.yaml`) because of some complications in how `lh-tactics` works. To
actually run liquid haskell while building, you must use

```sh
stack build --ghc-options="-fplugin=LiquidHaskell"
```

To run other examples, `cp` the right file from `props-done/` into `src/TIP/`.

## Running your own test

Make a new `stack` package, let's call it `test-package`.
```sh
stack new test-package
cd test-package/
```
Include the following in the package's dependencies:
```
dependencies:
  - liquidhaskell == 0.8.10.7
  - liquid-base == 4.15.0.0
  - template-haskell == 2.17.0.0
  - lh-tactics
```
Say you want to use `lh-tactics` in a module `Test`. Then the file `Test.hs`
should have the following structure, where `proof` is a definition that uses
proof macros:
```hs
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module Test where

import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core.Quote

--- ...

{-@ automatic-instances proof @-}
{-@
proof :: ... -- refined type signature
-@}
[tactic|
proof :: ... -- type signature
proof = ... -- tactics
|]
```

Then run `lh-tactics` like so in `test-package/`
```sh
stack clean
lh-tactics src/Test.hs:proof
```
This will give you some feedback, including syntax errors and the like. Then
finally, to verify your proof, run the following:
```sh
stack build --ghc-options="-fplugin=LiquidHaskell"
```
If `lh-tactics` succeeded, it should have commented out your original proof
macro usage and put a generated proof term directly underneath it.

## Data

The evaluation in _[Liquid Proof Macros][liquid-proof-macros]_ was based on the
data available in `data/`. In particular:
- `data/easy-inductives.md` shows which properties (from `props-done`) were
  successfully proven, and which of those only required "easy" proofs (via proof
  macros)
- `data/line-diffs.md` shows the differences in line counts between each
  property's file before/after running `lh-tactics`, and additional line
  count diffs for before/after running the liquid proof macros pruning procedure

## Resources

- _[Liquid Proof Macros][liquid-proof-macros]_

[liquid-proof-macros]: https://www.conference-publishing.com/download.php?Event=ICFPWS22HASKELLMAIN&Paper=e31f37ddb4671b0283a52fa225590e&Version=final


`stack build --ghc-options "-ddump-splices -fplugin=LiquidHaskell -fplugin-opt=LiquidHaskell:--compile-spec"`