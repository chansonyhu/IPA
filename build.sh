#!/bin/bash
rm -R bin
ant -f cpachecker-ipa.xml
rm cpachecker-summary.jar
mv out/production/cpachecker-summary bin
rm -R out
