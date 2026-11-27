#!/bin/bash
cd "$(dirname "$0")"
python3 game_scan.py 2 0.05 > out/scan_2.txt 2>&1
python3 game_scan.py 3 0.1 > out/scan_3.txt 2>&1
python3 game_scan.py 2x2 0.1 > out/scan_2x2.txt 2>&1
