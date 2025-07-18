It may be best to install these dependencies on a new "switch"
linked to this directory:

```
cd my-dir
opam switch create my-switch 4.14.2
opam switch link my-switch .
eval $(opam env)
```

Then, to install dependencies using `opam`:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

make builddep
```

Finally, run `make` to build the Rocq project, recompiling after making
changes to any files that the current one depends on.

If you are on macOS, you may have to export `CDFLAGS` and `LDFLAGS` so that
`zarith` can link against `gmp` properly. After doing this, reinstall `zarith`
and `coq-core`.
