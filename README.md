# SRLearn

A package for learning Statistical Relational Models with Gradient Boosting.

*It's basically BoostSRL but half the size.*

## Windows Quickstart

1. Open Windows Terminal in Administrator mode, and use [Chocolatey](https://chocolatey.org/) to install Maven and a Java Development Kit.

```bash
$ choco install openjdk
$ choco install maven
```

2. Clone and build the package.

```bash
$ git clone https://github.com/hayesall/SRLearn.git
$ cd .\SRLearn\
$ mvn package
```

3. Run a basic example:

```bash
`$ java -jar .\target\srlearn-jar-with-dependencies.jar -l .\data\Toy-Cancer\train\ -target cancer
```
``