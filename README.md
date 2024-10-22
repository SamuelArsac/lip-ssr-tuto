<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# lip-ssr-tuto






A tutorial for LIP members

## Meta

- Author(s):
  - Cyril Cohen (initial)
- License: [GNU Lesser General Public License v2.1](LICENSE)
- Compatible Coq versions: 8.18 to 8.20
- Additional dependencies:
  - Mathematical components version 2.2.0
  - Mathematical components algebra tactics 1.2.3
  - Mathematical components zify plugin 1.5.0
  - Mathematical components analysis library 1.5.0
- Coq namespace: `LipSsrTuto`
- Related publication(s): none

## Building and installation instructions

Unfortunately the Coq platform has not been release for 1 year
:confused:, so we have to rely on either of the following four options.

In all cases but the last you need to clone this repo and cd into it.

### Using opam
After having installed opam and configured it for Coq [cf official
doc](https://coq.inria.fr/opam-using.html), run:
```bash
opam install --deps-only .
make
```
You can now run your favorite editor, you may need to install your
favorite language server (i.e. `opam install coq-lsp` or
`opam install vscoq-language-server`)

### Using nix
After [installing nix](https://nixos.org/download/) and
[cachix](https://docs.cachix.org/installation), run once:
```bash
cachix use coq
cachix use coq-community
cachix use math-comp
cachix use cohencyril
```

Then, every time you want to use it you need to run (may take a few
minutes the first time)
```bash
nix-shell
make
```
You can now run your favorite editor, you **do not need** to install your
favorite language server (they are included in the shell)

### Using docker (warning, the image is > 17GB)

You need to [install docker](https://docs.docker.com/engine/install/).

Then start vscode with the
[`devcontainer`](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers)
extension, then click on "reopen in container" (or `F1` and type the latter).

### Using codespaces (limited in time)

Go to the repo and start a codespace ([Shortcut
here](https://github.com/codespaces/new?ref=main&repo=876092766))

## Documentation

Follow the lectures in order.
