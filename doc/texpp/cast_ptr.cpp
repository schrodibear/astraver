\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\begin{slshape}//@~\textbf{requires}~\textbf{\char'134 valid}(x);\end{slshape}~\\
void~zero(int*~x)~\{~\\
~~char~*c~=~(char*)x;~\\
~~*c~=~0;~\\
~~c++;~\\
~~*c~=~0;~\\
~~c++;~\\
~~*c~=~0;~\\
~~c++;~\\
~~*c~=~0;~\\
\}~\\
\end{flushleft}