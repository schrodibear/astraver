\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\begin{slshape}/*@~\textbf{requires}~\textbf{\char'134 valid}(i)~\&{}\&{}~\textbf{\char'134 valid}(j);~\\
~~@~\textbf{requires}~r~==~\textbf{\char'134 null}~||~\textbf{\char'134 valid}(r);~\\
~~@~\textbf{ensures}~*i~==~\textbf{\char'134 old}(*i)~\&{}\&{}~*j~==~\textbf{\char'134 old}(*j);~\\
~~@*/\end{slshape}~\\
int~max(int~*r,~int*~i,~int*~j)~\{~\\
~~\textbf{if}~(!r)~\textbf{return}~$-$1;~\\
~~*r~=~(*i~<~*j)~?~*j~:~*i;~\\
~~\textbf{return}~0;~\\
\}~\\
\end{flushleft}