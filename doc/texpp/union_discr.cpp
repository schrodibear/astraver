\begin{flushleft}\ttfamily\upshape\parindent 0pt
\textbf{union}~U~\{~\\
~~int~i;~\\
~~int*~p;~\\
\};~\\
~\\
\begin{slshape}//@~\textbf{requires}~\textbf{\char'134 valid}(x);\end{slshape}~\\
void~zero(\textbf{union}~U*~x)~\{~\\
~~x$-$>i~=~0;~\\
~~\begin{slshape}//@~assert~x$-$>i~==~0;\end{slshape}~\\
~~x$-$>p~=~(int*)malloc(sizeof(int));~\\
~~*x$-$>p~=~1;~\\
~~\begin{slshape}//@~assert~*x$-$>p~==~1;\end{slshape}~\\
\}~\\
\end{flushleft}