package edu.wisc.cs.will.Utils.condor.chirp;

import java.io.IOException;

/*
A ChirpInputStream gives a sequential binary interface to a read-only
file.  Users that require random-access I/O should see ChirpClient.
Users requiring a character-oriented interface to a Chirp file
should make use of an InputStreamReader like so:
<pre>
InputStreamReader in = new InputStreamReader(new ChirpInputStream(filename));
</pre> 
*/

public class ChirpInputStream extends java.io.InputStream {
	private final ChirpClient client;
	private final int fd;

	/*
	 * Create a new input stream attached to the named file. Use the Chirp server
	 * implicitly defined by the environment.
	 * @param p The file name.
	 */
	public ChirpInputStream( String p ) throws IOException {
		client = new ChirpClient();
		fd = client.open(p,"r",0);
	}

	/*
	 * Read bytes from the stream
	 * @param buffer The buffer to fill.
	 * @param pos The starting position in the buffer.
	 * @param length The number of bytes to read.
	 * @return The number of bytes actually read, or -1 at end-of-file.
	 * @throws IOException
	 */
	public int read( byte [] buffer, int pos, int length ) throws IOException {
		int response;
		response = client.read(fd,buffer,pos,length);
		if(response==0) {
			return -1;
		} else {
			return response;
		}
	}

	/*
	 * Read bytes from the stream.
	 * @param buffer The buffer to fill.
	 * @return The number of bytes actually read, or -1 at end-of-file.
	 */
	public int read( byte [] buffer ) throws IOException {
		return read(buffer,0,buffer.length);
	}

	/*
	 * Read one byte from the stream.
	 * @return The byte read, or -1 at end-of-file.
	 */
	public int read() throws IOException {
		byte [] temp = new byte[1];
		int actual = read(temp,0,1);
		if( actual>0 ) {
			return temp[0] >= 0 ? temp[0] : (256 + temp[0]);
		} else {
			return -1;
		}
	}

	public void close() throws IOException {
		client.close(fd);
	}
}


