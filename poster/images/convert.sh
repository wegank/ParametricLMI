#!/usr/bin/env bash

for i in *.svg; do
    rsvg-convert -h 256 $i -o ${i%.svg}.png
done
