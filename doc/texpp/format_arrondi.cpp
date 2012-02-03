\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\begin{slshape}\rmfamily\color{darkgreen}//~3~formats~possibles\end{slshape}~\\
\textbf{type}~float\_{}format~=~Single~|~Double~|~Quad~\\
~\\
\begin{slshape}\rmfamily\color{darkgreen}//~5~modes~d'arrondi~(norme~IEEE$-$754)\end{slshape}~\\
\textbf{type}~mode~=~nearest\_{}even~|~to\_{}zero~~\\
~~~~~~~~~~~~|~up~|~down~|~nearest\_{}away~\\
~\\
\begin{slshape}\rmfamily\color{darkgreen}//~arrondi~avec~exposant~non~borné\end{slshape}~\\
round\_{}float~:~float\_{}format,~mode,~real~$-$>~real~\\
~\\
\begin{slshape}\rmfamily\color{darkgreen}//~test~de~non$-$débordement~\end{slshape}~\\
max\_{}gen\_{}float~:~float\_{}format~$-$>~real~\\
\textbf{predicate}~~\\
~~~no\_{}overflow(f:float\_{}format,m:mode,x:real)~=~~\\
~~~abs\_{}real(round\_{}float(f,m,x))~<=~max\_{}gen\_{}float(f)~\\
\end{flushleft}