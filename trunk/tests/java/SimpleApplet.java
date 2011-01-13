// JAVACARD: will ask regtests to use Java Card API for this program

/*****************************

Very basic Java Card Applet to check non-regression of basic Java Card support

thanks to Peter Trommler <trommler@site.uottawa.ca>

********************/



import javacard.framework.APDU;
import javacard.framework.Applet;
import javacard.framework.ISO7816;
import javacard.framework.ISOException;
import javacard.framework.JCSystem;
import javacard.framework.OwnerPIN;
import javacard.security.*;

public class Card extends Applet {
	
    //##################################################
    //Instruction Variables
    //##################################################
    final static byte Card_Class = (byte)0x80;
    final static byte Card_Ins_Pin= (byte)0x02;
    final static byte Card_Ins_Auth=(byte)0x01;
    final static byte Card_Ins_Write= (byte) 0x05;
    final static byte Card_Ins_Del = (byte) 0x06;
    final static byte Card_Ins_Read = (byte) 0x07;
	
	
    //##################################################
    //Other Parameters
    //##################################################
    final static byte Key_Length = (byte) 0x84;
    final static short Data_Count = 10; 
    final static short Data_Len = 5;
    final static byte Term_Function_Writer =(byte) 0xAA;
    final static byte Term_Function_Reader = (byte)0x11;
	
    /**
     * Constructor for the Card.
     */
    Card(){
	// nothing to be done
    }

    //#####################################################
    //Applet Card install
    //####################################################
    public static void install(byte[] bArray, short bOffset, byte bLength) {
	// GP-compliant JavaCard applet registration
	new Card().register(bArray, (short) (bOffset + 1), bArray[bOffset]);
    }
	
    //####################################################
    //Here starts the good part.
    //###################################################
    public void process(APDU apdu) {
	//When the applet is selected, the card will be initialised!		
	if (selectingApplet()) {
	    return;
	}
		
	byte[] buf = apdu.getBuffer();
		
	//Returns an error if the Class  is wrong.
	if(buf[ISO7816.OFFSET_CLA]!= Card_Class){
	    ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
	}
		
	switch (buf[ISO7816.OFFSET_INS]) {
	    //Here is where the Signature from the terminal will be checked
	    //and also here is where will be decided to what functions
	    //the Terminal will have access to.
				
	    //Calls the Read Method	
	case Card_Ins_Read:
	    // for now just return OK SW1SW2=0x9000
	    break;
				
	default:
	    // good practice: If you don't know the INStruction, say so:
	    ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
	}
	return;
    }
}

