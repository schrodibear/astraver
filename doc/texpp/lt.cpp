\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
parameter~lt\_{}gen\_{}float~:~\\
x:gen\_{}float~$-$>~y:gen\_{}float~$-$>~~\\
\{~\}~\\
bool~\\
\{~~\\
is\_{}nan(x)~or~is\_{}nan(y)~$-$>~result~=~false~\\
and~\\
is\_{}finite(x)~and~is\_{}infinite(y)~$-$>~~\\
~~\textbf{if}~result~then~float\_{}sign(y)~=~Positive~\\
~~\textbf{else}~float\_{}sign(y)~=~Negative~\\
and~~\\
is\_{}infinite(x)~and~is\_{}finite(y)~$-$>~~\\
~~\textbf{if}~result~then~float\_{}sign(x)~=~Negative~\\
~~\textbf{else}~float\_{}sign(x)~=~Positive~\\
\end{flushleft}