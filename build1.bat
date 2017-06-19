ocamlc hw1.mli
ocamlc -safe-string hw1.ml -o t.exe
t.exe
echo "deleting all generated files"
@echo off
call clean.bat	