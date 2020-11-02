#!/bin/bash
sudo chmod o+wt '/sys/fs/cgroup/cpuset/' '/sys/fs/cgroup/memory/' '/sys/fs/cgroup/freezer/' '/sys/fs/cgroup/cpu,cpuacct/'
sudo swapoff -a
echo Starting baseline configuration...
benchexec quick-start-baseline.xml
echo Starting IPA configuration...
benchexec quick-start-ipa.xml
