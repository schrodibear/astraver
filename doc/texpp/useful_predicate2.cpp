\begin{flushleft}\ttfamily\upshape\parindent 0pt
\begin{slshape}\rmfamily\color{darkgreen}//~infinis~signés~:~+/$-$~infini~\end{slshape}~\\
\textbf{predicate}~is\_{}minus\_{}infinity(x:gen\_{}float)~=~~\\
~~~is\_{}infinite(x)~and~float\_{}sign(x)~=~Negative~\\
\textbf{predicate}~is\_{}plus\_{}infinity(x:gen\_{}float)~=~~\\
~~~is\_{}infinite(x)~and~float\_{}sign(x)~=~Positive~\\
~\\
\begin{slshape}\rmfamily\color{darkgreen}//~zéros~signés~:~$-$0~et~+0\end{slshape}~\\
\textbf{predicate}~is\_{}gen\_{}zero(x:gen\_{}float)~=~~\\
~~~is\_{}finite(x)~and~float\_{}value(x)~=~0.0~\\
~\\
\textbf{predicate}~is\_{}gen\_{}zero\_{}plus(x:gen\_{}float)~=~~\\
~~~is\_{}gen\_{}zero(x)~and~float\_{}sign(x)~=~Positive~\\
~\\
\textbf{predicate}~is\_{}gen\_{}zero\_{}minus(x:gen\_{}float)~=~~\\
~~~is\_{}gen\_{}zero(x)~and~float\_{}sign(x)~=~Negative~\\
\end{flushleft}