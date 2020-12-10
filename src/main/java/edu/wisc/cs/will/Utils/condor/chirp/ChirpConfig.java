package edu.wisc.cs.will.Utils.condor.chirp;

import edu.wisc.cs.will.Utils.condor.CondorFileReader;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.StringTokenizer;

/*
ChirpConfig represents the client configuration information needed
for a Chirp connection.  The constructor parses a configuration
file for a host, port, and cookie.  Inspector methods simply return
those values.
*/

class ChirpConfig {

	private final String host;
    private final String cookie;
	private final int port;

	/*
	 * Load configuration data from a file.
	 * @param filename The name of the file.
	 */
	ChirpConfig(String filename) throws IOException {
		BufferedReader br = new BufferedReader(new CondorFileReader(filename));
		StringTokenizer st = new StringTokenizer(br.readLine());

		host = st.nextToken();
		String portstr = st.nextToken();
		port = Integer.parseInt(portstr);
		cookie = st.nextToken();
	}

	/*
	 * @return The name of the server host.
	 */
	String getHost() {
		return host;
	}

	/*
	 * @return The port on which the server is listening.
	 */
	int getPort() {
		return port;
	}

	/*
	@return The cookie expected by the server.
	*/
	String getCookie() {
		return cookie;
	}
}
