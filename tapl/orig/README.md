original implementations from https://www.cis.upenn.edu/~bcpierce/tapl/resources.html#checkers

## OCaml installation
https://ocaml.org/docs/installing-ocaml
```shelll
# mac
$ brew install opam
# debian
$ sudo apt install opam
# nix
$ nix-env -i opam

$ opam init
# don't allow to add code to ~/.zshrc (it will polute PATH)

$ source ~/.opam/opam-init/complete.zsh2
$ eval $(opam env)
$ $ opam install ocaml-lsp-server odoc ocamlformat utop
```

## Configure Emacs
https://ocaml.org/docs/configuring-your-editor
```shell
$ opam install merlin tuareg
$ opam user-setup install
```
