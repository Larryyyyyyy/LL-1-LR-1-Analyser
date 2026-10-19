# Description

A toy.

# Usage

In `main.cpp` we bind the related files as dead route `./example/...` and remember to change before used.

```shell
g++ main.cpp -O2 -o main.exe
./main.exe
```

Use `graphviz` to transform `*.dot` to closure graph.

```shell
sudo apt install graphviz
dot -Tsvg lr_dfa.dot -o lr_dfa.svg
```

