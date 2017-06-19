ocamlc hw1.mli hw1_reduction.mli
ocamlc -safe-string hw1.ml hw1_reduction.ml -o t.exe
t.exe
echo "deleting all generated files"
@echo off
call clean.bat	