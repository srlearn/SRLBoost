# SRLBoost

A package for learning Statistical Relational Models with Gradient Boosting,
forked for use as [`srlearn's`](https://github.com/srlearn/srlearn) core.

## *It's basically [BoostSRL](https://starling.utdallas.edu/software/boostsrl/) but half the size and significantly faster.*

<img style="max-height: 400px;" src="https://raw.githubusercontent.com/srlearn/SRLBoost/master/docs/lines_of_code_graph.png" alt="Graph comparing the number of lines of code in each fork: BoostSRL, BoostSRL-Lite, and SRLBoost. SRLBoost is about half the size of BoostSRL.">

Graphs at commit [`cb952a4`](https://github.com/srlearn/SRLBoost/tree/cb952a486c57b0fdaee53a10e25a689f7951e6b4), measured
with [`cloc-1.84`](https://github.com/AlDanial/cloc).

## *How much faster?*

<img style="max-height: 500px;" src="https://raw.githubusercontent.com/srlearn/SRLBoost/master/docs/speed_test.png" alt="Box plots comparing the RDN learning time with SRLBoost, BoostSRL-Lite, and BoostSRL 1.1.1">

(*Smaller numbers are better.*)

This box plot compares the learning time (in seconds) for three data sets and three implementations of learning 
relational dependency networks. [`BoostSRL-Lite`](https://github.com/starling-lab/BoostSRL-Lite) was built from the
repository on GitHub, and [`BoostSRL_v1.1.1`](https://starling.utdallas.edu/software/boostsrl/) is the latest official
release.

Each data set included 4-5 cross validation folds, and these results were averaged over 10 runs. This appears to 
suggest that `SRLBoost` is at least twice as fast as other implementations.

With some parameter tuning we have sped this up even further.

<img style="max-height: 500px;" src="https://raw.githubusercontent.com/srlearn/SRLBoost/master/docs/cora_speed_test.png" alt="Box plots comparing learning time on the cora data set">

The tiny bar on the left shows the average `SRLBoost` time for Cora is around 17 seconds, compared to around 4.5 minutes for 
`BoostSRL-Lite` and `BoostSRL` (that's more like 15x faster).

However, on Cora this does lead to slightly degraded performance in AUC ROC, AUC PR, and conditional log likelihood (CLL);
shown in the table below.

| **Implementation** | **mean AUC ROC** | **mean AUC PR** | **mean CLL** | **mean F1** |
| :--- | :---: | :---: | :---: | :---: |
| SRLBoost | 0.61 | 0.93 | -0.27 | 0.96 |
| BoostSRL-Lite | 0.65 | 0.94 | -0.29| 0.96 |
| BoostSRLv1.1.1 | 0.65 | 0.94 | -0.29 | 0.78 |

[[Measurements used to produce this table are available online (`three_jar_comparison.csv`)]](https://gist.github.com/hayesall/106104f7fb335c87f0db5b9f9b5db0f9)

A main aim for this project is to have a faster library. 
We have made the faster parameters the defaults, and intend to expose them as things that users can tune in instances 
where slower, more effective learning is critical.

---

## Getting Started

SRLBoost project structure still closely mirrors other implementations.

We're using [Gradle](https://gradle.org/) to help with building and testing, targeting Java 8.

### Windows Quickstart

1. Open Windows Terminal in Administrator mode, and use [Chocolatey](https://chocolatey.org/) (or your preferred package manager) to install a Java Development Kit.

```bash
choco install openjdk
```

2. Clone and build the package.

```bash
git clone https://github.com/srlearn/SRLBoost.git
cd .\SRLBoost\
.\gradlew build
```

3. Learn with a basic data set (switching the `X.Y.Z`):

```bash
java -jar .\build\libs\srlboost-X.Y.Z.jar -l -train .\data\Toy-Cancer\train\ -target cancer
```

4. Query the model on the test set (again, swtiching the `X.Y.Z`)

```bash
java -jar .\build\libs\srlboost-X.Y.Z.jar -i -model .\data\Toy-Cancer\train\models\ -test .\data\Toy-Cancer\test\ -target cancer
```

### MacOS / Linux

1. Open your terminal (MacOS: <kbd>⌘</kbd> + <kbd>spacebar</kbd> + "Terminal"), and use [Homebrew](https://brew.sh) to install a Java Development Kit. (On Linux: `apt`, `dnf`, or `yum` depending on your Linux flavor).

```bash
brew install openjdk
```

2. Clone and build the package.

```bash
git clone https://github.com/srlearn/SRLBoost.git
cd SRLBoost/
./gradlew build
```

3. Run a basic example (switching the `X.Y.Z`):

```bash
java -jar build/libs/srlboost-X.Y.Z.jar -l -train data/Toy-Cancer/train/ -target cancer
```

4. Query the model on the test set (again, swtiching the `X.Y.Z`)

```bash
java -jar build/libs/srlboost-X.Y.Z.jar -i -model data/Toy-Cancer/train/models/ -test data/Toy-Cancer/test/ -target cancer
```
