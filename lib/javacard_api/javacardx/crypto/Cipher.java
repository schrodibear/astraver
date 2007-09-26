
package javacardx.crypto;
import javacard.security.*;

public class Cipher extends Object {

    static int MODE_DECRYPT;
    static int ENCRYPT_MODE;
    static int PRIVATE_KEY;
    static int PUBLIC_KEY;
    static int SECRET_KEY;
    static int UNWRAP_MODE;
    static int WRAP_MODE;

    byte[] doFinal();
    byte[] doFinal(byte[] input);
    int doFinal(byte[] output, int outputOffset);
    byte[] doFinal(byte[] input, int inputOffset, int inputLen);
    int doFinal(byte[] input, int inputOffset, int inputLen, byte[] output);
    int doFinal(byte[] input, int inputOffset, int inputLen, byte[] output, int outputOffset);
    int getBlockSize();
    byte[] getIV();
    int getOutputSize(int inputLen);
    void init(DESKey key, int opmode);
    byte[] update(byte[] input);
    byte[] update(byte[] input, int inputOffset, int inputLen);
    int update(byte[] input, int inputOffset, int inputLen, byte[] output);
    int update(byte[] input, int inputOffset, int inputLen, byte[] output, int outputOffset);
}


   
