@echo off
java -cp bin;cpachecker.jar;lib\*;lib\java\runtime\* -Xmx1200m -da org.sosy_lab.cpachecker.cmdline.CPAMain %*
