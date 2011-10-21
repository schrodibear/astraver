\begin{flushleft}\ttfamily\upshape\parindent 0pt
~\\
~\\
\begin{slshape}/*@~\textbf{predicate}~Swap\{L1,L2\}(int~*a,~integer~i,~integer~j)~=~\\
~~@~~~\textbf{\char'134 at}(a[i],L1)~==~\textbf{\char'134 at}(a[j],L2)~\&{}\&{}~\\
~~@~~~\textbf{\char'134 at}(a[j],L1)~==~\textbf{\char'134 at}(a[i],L2)~\&{}\&{}~\\
~~@~~~\textbf{\char'134 forall}~integer~k;~k~!=~i~\&{}\&{}~k~!=~j~\\
~~@~~~~~~~==>~\textbf{\char'134 at}(a[k],L1)~==~\textbf{\char'134 at}(a[k],L2);~\\
~~@*/\end{slshape}~\\
~\\
\begin{slshape}/*@~inductive~Permut\{L1,L2\}(int~*a,~integer~l,~integer~h)~\{~\\
~~@~~\textbf{case}~Permut\_{}refl\{L\}:~\\
~~@~~~\textbf{\char'134 forall}~int~*a,~integer~l,~h;~Permut\{L,L\}(a,~l,~h)~;~\\
~~@~~\textbf{case}~Permut\_{}sym\{L1,L2\}:~\\
~~@~~~~\textbf{\char'134 forall}~int~*a,~integer~l,~h;~\\
~~@~~~~~~Permut\{L1,L2\}(a,~l,~h)~==>~Permut\{L2,L1\}(a,~l,~h)~;~\\
~~@~~\textbf{case}~Permut\_{}trans\{L1,L2,L3\}:~\\
~~@~~~~\textbf{\char'134 forall}~int~*a,~integer~l,~h;~\\
~~@~~~~~~Permut\{L1,L2\}(a,~l,~h)~\&{}\&{}~Permut\{L2,L3\}(a,~l,~h)~==>~\\
~~@~~~~~~~~Permut\{L1,L3\}(a,~l,~h)~;~\\
~~@~~\textbf{case}~Permut\_{}swap\{L1,L2\}:~\\
~~@~~~~\textbf{\char'134 forall}~int~*a,~integer~l,~h,~i,~j;~\\
~~@~~~~~~~l~<=~i~<=~h~\&{}\&{}~l~<=~j~<=~h~\&{}\&{}~Swap\{L1,L2\}(a,~i,~j)~==>~\\
~~@~~~~~Permut\{L1,L2\}(a,~l,~h)~;~\\
~~@~\}~\\
~~@*/\end{slshape}~\\
~\\
\begin{slshape}/*@~\textbf{predicate}~Sorted\{L\}(int~*a,~integer~l,~integer~h)~=~\\
~~@~~~\textbf{\char'134 forall}~integer~i;~l~<=~i~<~h~==>~a[i]~<=~a[i+1]~;~\\
~~@*/\end{slshape}~\\
\end{flushleft}