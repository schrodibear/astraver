// #include "kfifo.h"

/*@
  @  predicate arrs_eq(unsigned char *y, unsigned char *x, integer shift, integer len) =
  @      (\forall integer i; (0<=i<len) ==> (y+shift)[i]==x[i]);
  @  predicate valid_kfifo(struct kfifo *f) =
  @		(\valid(f) && (f->size > 0) && (f->in <= f->out) && \valid_range(f->buffer,0, f->size-1));
  @      (\forall integer i; (0<=i<len) ==> (y+shift)[i]==x[i]);
  @*/

//#define smp_rmb()    { }
//#define smp_mb()    { }
//#define smp_wmb()    { }

//typedef unsigned int size_t;

/*@ requires (len>=0) && \valid_range(dst, 0, len-1) && \valid_range(src,0,len-1);
  @ ensures (arrs_eq(src, dst, 0, len) && (\result == dst));
  @*/
void* memcpy(unsigned char *dst, const unsigned char* src, unsigned int len)
{
	unsigned int i;
  /*@ loop invariant (0<=i<=len) && arrs_eq(src,dst,0,i);
	@ loop variant len-i;
    @*/
  for(i=0;i<len;i++)
    dst[i] = src[i];
  return dst;
}

/*@ requires \true;
  @ ensures ((\result==a && \result<b) || (\result==b && \result<=a));
  @*/
int min(int a, int b) {
	return ((a < b) ? a : b);
}
//#define min(a,b) ((a < b) ? a : b)


/**
 * kfifo_init - initialize a FIFO using a preallocated buffer
 * @fifo: the fifo to assign the buffer
 * @buffer: the preallocated buffer to be used.
 * @size: the size of the internal buffer, this has to be a power of 2.
 *
 */
void kfifo_init(struct kfifo *fifo, unsigned char *buffer, unsigned int size)
{
	fifo->buffer = buffer;
	fifo->size = size;
	fifo->in = fifo->out = 0;
}

/**
 * kfifo_reset - removes the entire FIFO contents
 * @fifo: the fifo to be emptied.
 */
void kfifo_reset(struct kfifo *fifo)
{
	fifo->in = fifo->out = 0;
}

/**
 * kfifo_size - returns the size of the fifo in bytes
 * @fifo: the fifo to be used.
 */
unsigned int kfifo_size(struct kfifo *fifo)
{
	return fifo->size;
}

/**
 * kfifo_len - returns the number of used bytes in the FIFO
 * @fifo: the fifo to be used.
 */
/*@ requires (\valid(fifo) && (fifo->size > 0) && \valid_range(fifo->buffer,0, fifo->size-1);
  @ ensures \result == fifo->in - fifo->out;
  @*/
unsigned int kfifo_len(struct kfifo *fifo)
{
//	unsigned int	out;
//
//	out = fifo->out;
//	smp_rmb();
//	return fifo->in - out;

	return fifo->in - fifo->out;
}

/**
 * kfifo_avail - returns the number of bytes availale in the FIFO
 * @fifo: the fifo to be used.
 */
unsigned int kfifo_avail(struct kfifo *fifo)
{
	return kfifo_size(fifo) - kfifo_len(fifo);
}

unsigned int __kfifo_off(struct kfifo *fifo, unsigned int off)
{
	return off & (fifo->size - 1);
}

void __kfifo_add_in(struct kfifo *fifo,unsigned int off)
{
//	smp_wmb();
	fifo->in += off;
}

void __kfifo_add_out(struct kfifo *fifo,unsigned int off)
{
//	smp_mb();
	fifo->out += off;
}


void __kfifo_in_data(struct kfifo *fifo,
		const unsigned char *from, unsigned int len, unsigned int off)
{
	unsigned int l;

	/*
	 * Ensure that we sample the fifo->out index -before- we
	 * start putting bytes into the kfifo.
	 */
	smp_mb();

//	printf("kfifo_in_data off=%d in=%d out=%d\n", off, fifo->in, fifo->out);
	off = __kfifo_off(fifo, fifo->in + off);
//	printf("kfifo_in_data off=%d in=%d out=%d, len=%d, size=%d\n",off,fifo->in,fifo->out, len, fifo->size);

	/* first put the data starting from fifo->in to buffer end */
	l = min(len, fifo->size - off);
	memcpy(fifo->buffer + off, from, l);

	/* then put the rest (if any) at the beginning of the buffer */
	memcpy(fifo->buffer, from + l, len - l);
}


/**
 * kfifo_in - puts some data into the FIFO
 * @fifo: the fifo to be used.
 * @from: the data to be added.
 * @len: the length of the data to be added.
 *
 * This function copies at most @len bytes from the @from buffer into
 * the FIFO depending on the free space, and returns the number of
 * bytes copied.
 */
unsigned int kfifo_in(struct kfifo *fifo, const unsigned char *from, unsigned int len)
{
	len = min(kfifo_avail(fifo),len);

	__kfifo_in_data(fifo, from, len, 0);
	__kfifo_add_in(fifo, len);
	return len;
}

void __kfifo_out_data(struct kfifo *fifo,
		unsigned char *to, unsigned int len, unsigned int off)
{
	unsigned int l;

	/*
	 * Ensure that we sample the fifo->in index -before- we
	 * start removing bytes from the kfifo.
	 */
	smp_rmb();

	off = __kfifo_off(fifo, fifo->out + off);

	/* first get the data from fifo->out until the end of the buffer */
	l = min(len, fifo->size - off);
	memcpy(to, fifo->buffer + off, l);

	/* then get the rest (if any) from the beginning of the buffer */
	memcpy(to + l, fifo->buffer, len - l);
}


/**
 * kfifo_out - gets some data from the FIFO
 * @fifo: the fifo to be used.
 * @to: where the data must be copied.
 * @len: the size of the destination buffer.
 *
 * This function copies at most @len bytes from the FIFO into the
 * @to buffer and returns the number of copied bytes.
 */

/*@ requires (\valid_kfifo(fifo) && (fifo->size > 0) && \valid_range(fifo->buffer,0, fifo->size-1);
  @ ensures (\result == ((fifo->len < len)?fifo->len:len) && fifo \old() ;
  \forall integer ind;
  \old(fifo->size) == fifo->size
  @*/
unsigned int kfifo_out(struct kfifo *fifo, unsigned char *to, unsigned int len)
{
	kfifo_len(fifo)
	len = min(kfifo_len(fifo), len);

	__kfifo_out_data(fifo, to, len, 0);
	__kfifo_add_out(fifo, len);

	return len;
}
