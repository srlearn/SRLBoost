# BoostSRL Reference Implementation

This is a reference implementation for BoostSRL, shortly before the 1.0 release.
This contains Shuo Yang's soft-rfgb implementation, but none of the other new features.

- [Tushar's Documentation](http://pages.cs.wisc.edu/~tushar/Boostr/)

## Getting Started

Packaging is done using Maven, and requires Java 1.8 or higher.

```bash
$ jenv exec mvn package
```

There is not a `-help` flag implemented, but running it with one will crash the program and 
print help information when it does.

```bash
$ java -jar target/boostsrl-0.9.0-jar-with-dependencies.jar -help 
```
