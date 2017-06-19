ocamlc hw1.mli hw1_reduction.mli hw2_unify.mli hw2_inference.mli
ocamlc -safe-string hw1.ml hw1_reduction.ml hw2_unify.ml hw2_inference.ml -o t.exe
t.exe
echo "deleting all generated files"
@echo off
call clean.bat	