#!/bin/sh

omake inez.top
exec ./inez.top -init inez.top.init
