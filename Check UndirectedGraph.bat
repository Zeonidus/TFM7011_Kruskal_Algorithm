@echo off
java -jar "E:\Downloads\openjml\openjml.jar" -prover z3_4_3 -exec "E:\Downloads\z3-4.3.0-x64\bin\z3.exe" -noPurityCheck UndirectedGraph.java
pause