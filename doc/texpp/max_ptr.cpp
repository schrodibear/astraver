\begin{flushleft}\ttfamily\upshape\parindent 0pt
\begin{slshape}/*@~\textbf{requires}~\textbf{\char'134 valid}(i)~\&{}\&{}~\textbf{\char'134 valid}(j);~\\
~~@~\textbf{requires}~r~==~\null~||~\textbf{\char'134 valid}(r);~\\
~~@~\textbf{assigns}~*r;~\\
~~@~behavior~zero:~\\
~~@~~~assumes~r~==~\null;~\\
~~@~~~\textbf{assigns}~\textbf{\char'134 nothing};~\\
~~@~~~\textbf{ensures}~\textbf{\char'134 result}~==~$-$1;~\\
~~@~behavior~normal:~\\
~~@~~~assumes~\textbf{\char'134 valid}(r);~\\
~~@~~~\textbf{assigns}~*r;~\\
~~@~~~\textbf{ensures}~*r~==~((*i~<~*j)~?~*j~:~*i);~\\
~~@~~~\textbf{ensures}~\textbf{\char'134 result}~==~0;~\\
~~@*/\end{slshape}~\\
int~max(int~*r,~int*~i,~int*~j)~\{~\\
~~\textbf{if}~(!r)~\textbf{return}~$-$1;~\\
~~*r~=~(*i~<~*j)~?~*j~:~*i;~\\
~~\textbf{return}~0;~\\
\}~\\
\end{flushleft}