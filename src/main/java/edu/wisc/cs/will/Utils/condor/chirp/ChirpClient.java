// TODO(@hayesall): There are three variables that are "never" used, but they seem to be used in other files.
//		This will take a bit more time to refactor.

package edu.wisc.cs.will.Utils.condor.chirp;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;

/**
 * A ChirpClient object represents the connection between a client and
 * a Chirp server.  The methods of this object correspond to RPCs in
 * the Chirp protocol, and are very similar to standard UNIX I/O operations.
 * Those looking for a more Java-style stream interface to Chirp should
 * see the ChirpInputStream and ChirpOutputStream objects.
 */

public class ChirpClient {

	private OutputStream output=null;
	private InputStream input=null;
	final private String encoding = "US-ASCII";

	/**
	 * Connect and authenticate to the default Chirp server.
	 * Determine the "default" from a variety of environmental concerns.
	 * If running within Condor, then Condor will set up the environment
	 * to proxy I/O through the starter back to the submit site.
	 */
	public ChirpClient() throws IOException {
		ChirpConfig config;
		try {
			String filename = System.getProperty("chirp.config");
			if(filename==null) throw new ChirpError("system property chirp.config is not defined!");
			config = new ChirpConfig(filename);
		} catch( Exception e ) {
			throw new ChirpError(e);
		}
		connect(config.getHost(),config.getPort());
		cookie(config.getCookie());
	}

	/**
	 * Connect to a given Chirp server. The caller must pass a cookie before using any other methods.
	 * Condor users should use the no-argument constructor instead.
	 * @param host The server host.
	 * @param port The server port.
	 */
	ChirpClient(String host, int port) throws IOException {
		connect(host,port);
	}

	private void connect( String host, int port ) throws IOException {
		Socket socket = new Socket(host, port);
		output = socket.getOutputStream();
		input = socket.getInputStream();
	}

	/**
	 * Present a 'cookie' string to a Chirp server. This call must be done before any
	 * other Chirp calls. If it is not, other methods are likely to throw exceptions
	 * indicating "not authenticated."
	 * @param c The cookie to present
	 */
	private void cookie(String c) throws IOException {
		simple_command("cookie "+ChirpWord(c)+"\n");	
	}

	/**
	 * Open a file.
	 * @param path The path to the file to open.
	 * @param flags A string of characters that state how the file is to be used. (r,w,t,c,x,a)
	 *              - r: open for reading
	 *              - w: open for writing
	 *              - t: truncate before use
	 *              - c: create if it does not exist, succeed otherwise
	 *              - x: modifies 'c' to fail if the file already exists
	 *              - a: modifies 'w' to always append
	 * @param mode If created, the initial UNIX access mode.
	 * @return An integer file descriptor that may be used with later calls.
	 */
	public int open( String path, String flags, int mode ) throws IOException {
		return simple_command("open "+ChirpWord(path)+" "+flags+" "+mode+"\n");
	}

	/**
	 * Same as the three-argument `open`, but the server selects a default initial UNIX mode.
	 */
	public int open(String path, String flags) throws IOException {
		return open(path, flags,0777);
	}

	/**
	 * Close a file.
	 * @param fd The file descriptor to close.
	 */
	public void close( int fd ) throws IOException {
		simple_command("close "+fd+"\n");
	}

	/**
	 * Read data from a file. This method is free to read any number of bytes less than or equal to the parameter
	 * 'length'. A result of zero indicates end of file.
	 * @param fd The file descriptor to read.
	 * @param buffer The data buffer to fill.
	 * @param pos The position in the buffer to start.
	 * @param length The maximum number of elements to read.
	 * @return The number of elements actually read.
	 */
	public int read( int fd, byte [] buffer, int pos, int length ) throws IOException {
		// TODO(@hayesall): In almost every other case, end-of-file is indicated by -1
		int response,actual;

		try {
			String line = "read " + fd + " " + length + "\n";
			byte [] bytes = line.getBytes(encoding);
			output.write(bytes,0,bytes.length);
			output.flush();
			response = getResponse();
			if(response>0) {
				actual = fullRead(buffer,pos,response);
				if(actual!=response) throw new ChirpError("server disconnected");
			}
		} catch( IOException e ) {
			throw new ChirpError(e);
		}
		return returnOrThrow(response);
	}

	/**
	 * Write data to a file. This method is free to write any number of elements less than or equal to the parameter
	 * 'length'.  A result of zero indicates end of file.
	 * @param fd The file descriptor to write.
	 * @param buffer The data buffer to use.
	 * @param pos The position in the buffer to start.
	 * @param length The maximum number of elements to write.
	 * @return The number of elements actually written.
	 */
	public int write(int fd, byte [] buffer, int pos, int length) throws IOException {
		int response;

		try {
			String line = "write " + fd + " " + length + "\n";
			byte [] bytes = line.getBytes(encoding);
			output.write(bytes,0,bytes.length);
			output.write(buffer,pos,length);
			output.flush();
			response = getResponse();
		} catch( IOException e ) {
			throw new ChirpError(e);
		}
		return returnOrThrow(response);
	}

	/** Seek from the beginning of a file. */
	public static final int SEEK_SET=0;

	/** Seek from the current position. */
	public static final int SEEK_CUR=1;

	/** Seek from the end of a file. */
	public static final int SEEK_END=2;

	/**
	 * Delete a file.
	 * @param name The name of the file.
	 */
	public void unlink( String name ) throws IOException {
		simple_command("unlink " + ChirpWord(name) + "\n");
	}

	/**
	 * Rename a file.
	 * @param name The old name.
	 * @param new_name The new name.
	 */
	public void rename(String name, String new_name) throws IOException {
		simple_command("rename "+ChirpWord(name)+" "+ChirpWord(new_name)+"\n");
	}

	/**
	 * Create a directory.
	 * @param name The directory name.
	 * @param mode The initial UNIX access mode.
	 */
	private void mkdir(String name, int mode) throws IOException {
		simple_command("mkdir " + ChirpWord(name) + " " + mode + "\n");
	}

	/**
	 * Create a directory. The server selects default initial permissions for the directory.
	 * @param name The directory name.
	 */
	public void mkdir( String name ) throws IOException {
		mkdir(name,0777);
	}

	public int version() throws IOException {
		return simple_command("version\n");
	}

	public String lookup( String path ) throws IOException {
		String url = null;
		int response = simple_command("lookup "+ChirpWord(path)+"\n");
		if(response>0) {
			byte [] buffer = new byte[response];
			int actual = fullRead(buffer,0,response);
			if(actual!=response) throw new ChirpError("server disconnected");
			url = new String(buffer,0,response,encoding);
		}
		returnOrThrow(response);
		return url;
	}

	public void constrain( String expr ) throws IOException {
		simple_command("constrain "+" "+ChirpWord(expr)+"\n");
	}

	private int simple_command(String cmd) throws IOException {
		int response;
		try {
			byte [] bytes = cmd.getBytes(encoding);
			output.write(bytes,0,bytes.length);
			output.flush();
			response = getResponse();
		} catch( IOException e ) {
			throw new ChirpError(e);
		}
		return returnOrThrow(response);
	}

	private String ChirpWord(String cmd) {
		StringBuilder buf = new StringBuilder();

		for (int i=0; i<cmd.length(); i++) {
			char ch = cmd.charAt(i);
			switch(ch) {
			case '\\':
			case ' ':
			case '\n':
			case '\t':
			case '\r':
				buf.append("\\");
			default:
			    buf.append(ch);
			}
		}
		return buf.toString();
	}

	private int returnOrThrow( int code ) throws IOException {
		if(code>=0) {
			return code;
		} else switch(code) {
			case -1:
				throw new ChirpError("couldn't authenticate");
			case -2:
				throw new IOException("permission denied");
			case -3:
				throw new FileNotFoundException();
			case -4:
				throw new IOException("file already exists");
			case -5:
				throw new IOException("argument too big");
			case -6:
				throw new ChirpError("out of space");
			case -7:
				throw new OutOfMemoryError();
			case -8:
				throw new IOException("invalid request");
			case -9:
				throw new IOException("too many files open");
			case -10:
				throw new IOException("file is busy");
			case -11:
				throw new IOException("try again");
			default:
				throw new ChirpError("unknown error");
		}
	}

	private int fullRead( byte [] buffer, int offset, int length ) throws IOException {
		int total=0;
		int actual;

		while(length>0) {
			actual = input.read(buffer,offset,length);
			if(actual==0) {
				break;
			} else {
				offset += actual;
				length -= actual;
				total += actual;
			}
		}
		return total;
	}

	private int getResponse() throws IOException {
		StringBuilder line= new StringBuilder();
		String digit;
		byte [] b = new byte[1];

		while(true) {
			b[0] = (byte) input.read();
			digit = new String(b,0,1,encoding);

			if(digit.charAt(0)=='\n') {
				if(line.length()>0) {
					return Integer.parseInt(line.toString());
				}
			} else {
				line.append(digit);
			}
		}
	}
}

class ChirpError extends Error {
	ChirpError( String s ) {
		super("Chirp: "+ s);
	}
	ChirpError( Exception e ) {
		super("Chirp: " +e.toString());
	}

}



