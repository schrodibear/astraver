\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
~\\
Definition~round\_{}float~(f~:~float\_{}format)~~\\
~~~~~~~~~~~~~~~~~~~~~~~(m~:~mode)~(x:R)~:=~\\
match~f~with~\\
|~Single~=>~gappa\_{}rounding~~\\
~~~~~~~(rounding\_{}float~(round\_{}mode~m)~24~149)~x~\\
|~Double~=>~gappa\_{}rounding~~\\
~~~~~~~(rounding\_{}float~(round\_{}mode~m)~53~1074)~x~\\
end.~\\
\end{flushleft}