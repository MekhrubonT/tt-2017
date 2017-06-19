ocamlc hw2_unify.mli
ocamlc -safe-string hw2_unify.ml -o t.exe
t.exe
echo "deleting all generated files"
@echo off
call clean.bat	