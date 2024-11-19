#!/bin/bash

flag=$1

rm output.txt
# Loop through all files in the "traces" directory
for file in traces/*; do
  # Run the mdriver command with the current file
  echo "====================================================="
  ./mdriver "$flag" -f "$file"
done >> output.txt
