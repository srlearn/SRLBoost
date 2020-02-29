# SRLBoost

A package for learning Statistical Relational Models with Gradient Boosting,
making up [`srlearn's`](https://github.com/hayesall/srlearn) core.

*It's basically BoostSRL, but half the size and twice as fast.*

![Graph comparing the number of lines of code in each fork: BoostSRL, BoostSRL-Lite, and SRLBoost. SRLBoost is about half the size of BoostSRL.](https://raw.githubusercontent.com/hayesall/SRLBoost/master/docs/lines_of_code_graph.png)

Graph at commit [`8725032`](https://github.com/hayesall/SRLBoost/tree/8725032ffee2f0390038e80b9635e2f65be03fbc).

## Windows Quickstart

1. Open Windows Terminal in Administrator mode, and use [Chocolatey](https://chocolatey.org/) to install Maven and a Java Development Kit.

```bash
$ choco install openjdk
$ choco install maven
```

2. Clone and build the package.

```bash
$ git clone https://github.com/hayesall/SRLBoost.git
$ cd .\SRLBoost\
$ mvn package
```

3. Run a basic example:

```bash
$ java -jar .\target\srlboost-jar-with-dependencies.jar -l .\data\Toy-Cancer\train\ -target cancer
```

## MacOS / Linux

1. Open your terminal (MacOS: <kbd>⌘</kbd> + <kbd>spacebar</kbd> + "Terminal"), and use [Homebrew](https://brew.sh) to install Maven and a Java Development Kit. (On Linux: `apt`, `dnf`, or `yum` depending on your Linux flavor).

```bash
$ brew install openjdk
$ brew install maven
```

2. Clone and build the package.

```bash
$ git clone https://github.com/hayesall/SRLBoost.git
$ cd SRLBoost/
$ mvn package
```

3. Run a basic example:

```bash
$ java -jar target/srlboost-jar-with-dependencies.jar -l data/Toy-Cancer/train/ -target cancer
```
