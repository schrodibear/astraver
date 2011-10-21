\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\begin{slshape}/*@~\textbf{requires}~\textbf{\char'134 valid}(i)~\&{}\&{}~\textbf{\char'134 valid}(j);~\\
~~@~\textbf{requires}~r~==~\textbf{\char'134 null}~||~\textbf{\char'134 valid}(r);~\\
~~@~\textbf{assigns}~*r;~\\
~~@~\textbf{behavior}~zero:~\\
~~@~~~\textbf{assumes}~r~==~\textbf{\char'134 null};~\\
~~@~~~\textbf{assigns}~\textbf{\char'134 nothing};~\\
~~@~~~\textbf{ensures}~\textbf{\char'134 result}~==~$-$1;~\\
~~@~\textbf{behavior}~normal:~\\
~~@~~~\textbf{assumes}~\textbf{\char'134 valid}(r);~\\
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