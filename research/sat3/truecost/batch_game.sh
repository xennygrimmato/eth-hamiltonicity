#!/bin/bash
cd "$(dirname "$0")"
python3 game_true.py 2 9 > out/game_2.txt 2>&1
python3 game_true.py 3 9 > out/game_3.txt 2>&1
python3 game_true.py 2x2 9 short > out/game_2x2.txt 2>&1
python3 game_true.py 4 9 short > out/game_4.txt 2>&1
python3 game_true.py 5 9 short > out/game_5.txt 2>&1
