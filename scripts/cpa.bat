@echo off
set params=""

set OLDPATH=%PATH%
set PATH=%PATH%;lib\native\x86-windows
java -cp bin;cpachecker.jar;lib\*;lib\java\runtime\* -Xmx10000m  org.sosy_lab.cpachecker.cmdline.CPAMain %*
set PATH=%OLDPATH%
