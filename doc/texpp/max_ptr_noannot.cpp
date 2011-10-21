\begin{flushleft}\ttfamily\upshape\parindent 0pt
int~max(int~*r,~int*~i,~int*~j)~\{~\\
~~\textbf{if}~(!r)~\textbf{return}~$-$1;~\\
~~*r~=~(*i~<~*j)~?~*j~:~*i;~\\
~~\textbf{return}~0;~\\
\}~\\
\end{flushleft}