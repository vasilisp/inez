#!/bin/sh

omake -j3 inez.top
exec ./inez.top -init inez.top.init
