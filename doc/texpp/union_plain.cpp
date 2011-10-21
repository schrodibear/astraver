\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\textbf{union}~U~\{~\\
~~int~i;~\\
~~\textbf{struct}~\{~short~s1;~short~s2;~\}~s;~\\
\};~\\
~\\
\begin{slshape}//@~\textbf{requires}~\textbf{\char'134 valid}(x);\end{slshape}~\\
void~zero(\textbf{union}~U*~x)~\{~\\
~~x$-$>i~=~0;~\\
~~\begin{slshape}//@~assert~x$-$>s.s1~==~0;\end{slshape}~\\
~~\begin{slshape}//@~assert~x$-$>s.s2~==~0;\end{slshape}~\\
\}~\\
\end{flushleft}