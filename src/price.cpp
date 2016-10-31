// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2012 The Bitcoin developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.
#ifdef _MSC_VER
    #include <stdint.h>

    #include "msvc_warnings.push.h"
#endif

#include "db.h"
#include "net.h"
#include "strlcpy.h"

#include <vector>

using std::string;
using std::runtime_error;
using std::vector;

const int 
    nArbitraryShortTimeInMilliseconds = nTenMilliseconds;
CCriticalSection 
    cs_price;  // just want one call to getYACprice to not
               // interrupt another call to the same function.

#ifdef WIN32
static const int
    nDefaultCharacterOffset = 3,
    nUnusualCharacterOffset = 2;
CProvider aBTCtoYACProviders[] = 
    {    
        {   
            "data.bter.com",            // sDomain
            "last",                     // sPriceRatioKey
            "/api/1/ticker/yac_btc",    // sApi
            nDefaultCharacterOffset
        }
        ,
        {   
            "pubapi2.cryptsy.com",      
            "lasttradeprice",   
            "/api.php?method=singlemarketdata&marketid=11", 
            nDefaultCharacterOffset 
        }
    };
CProvider aCurrencyToBTCProviders[] = 
    {
        {   
            "btc.blockr.io",
            "value",
            "/api/v1/coin/info",
            nUnusualCharacterOffset    
        }
        ,
        {   
            "api.bitcoinvenezuela.com",
            "USD",
            "/",
            nUnusualCharacterOffset
        }
        ,
        {   
            "pubapi2.cryptsy.com",
            "lastdata",
            "/api.php?method=singlemarketdata&marketid=2",
            nDefaultCharacterOffset
        }
    };
std::vector< CProvider > vBTCtoYACProviders;
std::vector< CProvider > vUSDtoBTCProviders;

bool recvAline( SOCKET &hSocket, string & strLine )
{
    char 
        c;
    int
        nBytes;

    do
    {
        nBytes = recv(hSocket, &c, 1, 0);   // better be one or zero!

        if (1 == nBytes)
        {   // OK
            strLine += c;
            if( '\n' == c )  // the signal for a line received
                break;
        }
        else
        {
            if (SOCKET_ERROR == nBytes) // error, which error? Some aren't
            {
                int 
                    nErr = WSAGetLastError();

                if (nErr == WSAEMSGSIZE)
                    continue;
                if (
                    nErr == WSAEWOULDBLOCK || 
                    nErr == WSAEINTR || 
                    nErr == WSAEINPROGRESS
                   )
                {
                    Sleep( nArbitraryShortTimeInMilliseconds );
                    continue;
                }
                // else it was something worthy of consideration?
            }
            if (!strLine.empty() )
                break;
            if (0 == nBytes)
            {   // done, socket closed
                return false;
            }
            else
            {   // socket error
                int 
                    nErr = WSAGetLastError();
                printf("recv failed: error %d\n", nErr);
                clearLocalSocketError( hSocket );
                return false;
            }
        }
    }
    while( true );
    return true;
}

//_____________________________________________________________________________
static bool read_in_new_provider( std::string sKey, std::vector< CProvider > & vProviders )
{
    // here is where we should read in new providers from the configuration file
    // arguments, and add them to the vectors we already have.  This way we don't
    // have to recompile if there is even a temporary failure with a web provider.
    bool
        fProviderAdded;

    //fProviderAdded = IsProviderAdded( key, vProviders );

    std::string
        sProvider = GetArg( sKey, "" );

    static const int
        nArbitrayUrlDomainLength = 200,
        nArbitrayUrlArgumentLength = 200;

    CProvider 
        cNewProvider;

    if( "" != sProvider )
    {
        string
            sTemp = "%200[^,],%200[^,],%200[^,],%d";

        if( fPrintToConsole )
        {
            printf( "scan string: %s\n", sTemp.c_str() );
        }
        printf( "received provider string:\n" );
        {
            printf( "%s\n", sProvider.c_str() );
        }
        if( nArbitrayUrlArgumentLength < (int)sProvider.length() )
        {   // could be trouble
            if( fPrintToConsole )
            {
                printf( "scan string: %s\n", sTemp.c_str() );
                printf( "Error: Probably too long?\n", sTemp.c_str() );
            }
            return false;
        }
        char
            caDomain[ nArbitrayUrlDomainLength + 1 ],
            caKey[ nArbitrayUrlDomainLength + 1 ],
            caApi[ nArbitrayUrlArgumentLength + 1 ];
        int
            nOffset,
            nPort;
        int
            nConverted = sscanf( 
                                sProvider.c_str(),
                                sTemp.c_str(),
                                caDomain,
                                caKey,
                                caApi,
                                &nOffset
                               );
        if( 4 == nConverted )
        {
            cNewProvider.sDomain        = caDomain;
            cNewProvider.sPriceRatioKey = caKey;
            cNewProvider.sApi           = caApi;
            cNewProvider.nOffset        = nOffset;
            vProviders.insert( vProviders.begin(), cNewProvider );
          //vBTCtoYACProviders.push_back( cNewProvider );
          //nIndexBtcToYac = 0;
            if( fPrintToConsole )
            {
                printf( "adding new provider:"
                        "\n"
                        "%s\n%s\n%s\n%d"
                        "\n",
                        cNewProvider.sDomain.c_str(),
                        cNewProvider.sPriceRatioKey.c_str(),
                        cNewProvider.sApi.c_str(),
                        cNewProvider.nOffset 
                      );
            }
            return true;
        }
        else
        {
            printf( "error parsing configuration file for provider, found string:"
                   "\n"
                   "%s"
                   "\n",
                   sProvider.c_str()
                  );
        }
    }
    return false;
}

//_____________________________________________________________________________
static void build_vectors()
{
    const int
        array_sizeUtoB = (int)( sizeof( aCurrencyToBTCProviders ) / sizeof( aCurrencyToBTCProviders[ 0 ] ) ),
        array_sizeBtoY = (int)( sizeof( aBTCtoYACProviders ) / sizeof( aBTCtoYACProviders[ 0 ] ) );

    for( int index = 0; index < array_sizeUtoB; ++index )
    {
        vUSDtoBTCProviders.push_back( aCurrencyToBTCProviders[ index ] );
    }
    for( int index = 0; index < array_sizeBtoY; ++index )
    {
        vBTCtoYACProviders.push_back( aBTCtoYACProviders[ index ] );
    }
}
//_____________________________________________________________________________

void initialize_price_vectors( int & nIndexBtcToYac, int & nIndexUsdToBtc )
{
    build_vectors();
    if( read_in_new_provider( "-btcyacprovider", vBTCtoYACProviders ) )
        nIndexBtcToYac = 0;
    if( read_in_new_provider( "-usdbtcprovider", vUSDtoBTCProviders) )
        nIndexUsdToBtc = 0;
}
//_____________________________________________________________________________
// this is the only section that needs a non Windows bit of code
// in this class, the ctor needs to be 'linux-ed', in other words
// how does one initialize and connect a socket in a non Windows environment?
// The MSVC++ & gcc in Windows versions work fine
class CdoSocket
{
private:
    struct hostent 
        *host;
    SOCKET 
        SocketCopy;

    CdoSocket( const CdoSocket & );
    CdoSocket &operator = ( const CdoSocket & );

public:
    explicit CdoSocket( SOCKET & Socket, const string & sDomain, const int & nPort = DEFAULT_HTTP_PORT )
    {
        Socket = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
        
        host = gethostbyname( sDomain.c_str() );

        if( NULL != host )
        {
            SOCKADDR_IN 
                SockAddr;

            SockAddr.sin_port = htons( (unsigned short)nPort ); // was 80
            SockAddr.sin_family = AF_INET;
            SockAddr.sin_addr.s_addr = *((unsigned long*)host->h_addr); //  null ptr if net is down!!

            //cout << "Connecting...\n";

            int
                nResult = connect(Socket,(SOCKADDR*)(&SockAddr),sizeof(SockAddr) );

            if ( SOCKET_ERROR == nResult )
            {
                std::string
                    sS = strprintf(
                                    "Could not connect"
                                    "connect function failed with error: %d\n", 
                                    WSAGetLastError()
                                  );
                clearLocalSocketError( Socket );
                nResult = closesocket(Socket);
                if (nResult == SOCKET_ERROR)
                    wprintf(L"closesocket function failed with error: %ld\n", WSAGetLastError());
                //WSACleanup();
                throw runtime_error(
                        "getYACprice\n"
                        "Could not connect?"
                                   );
            }
            SocketCopy = Socket;
        }
        else    // network is down?
        {
            throw runtime_error(
                                "getYACprice\n"
                                "Network is down?"
                               );
        }
    }

    ~CdoSocket()
    {
        clearLocalSocketError( SocketCopy );
        closesocket( SocketCopy );
    }    
};
//_____________________________________________________________________________
static bool GetMyExternalWebPage(
                          const string & sDomain,
                          const string & skey,
                          const char* pszTheFullUrl, 
                          string & strBuffer, 
                          double &dPrice,
                          const int & nOffset,
                          const int & nPort
                         )
{
    // here we should
    // pick a provider from vBTCtoYACProviders & vUSDtoBTCProviders
    // attempt a price, if fail, try another provider until OK, or error return
    // 
    //
    {
        LOCK( cs_price );
        SOCKET 
#ifdef _MSC_VER
            hSocket = NULL;
#else
            hSocket = 0;
#endif
        try
        {
            if( DEFAULT_HTTP_PORT != nPort )
            {
                CdoSocket 
                    CthisSocketConnection( 
                                          hSocket, 
                                          sDomain,
                                          nPort
                                         );
            }
            else
            {
                CdoSocket 
                    CthisSocketConnection( 
                                          hSocket, 
                                          sDomain           // for gethostbyname()
                                         );                 //RAII attempt on the socket!?
            }
        }
        catch( std::exception &e )
        {
            printf( "%s\n", (string("error: ") + e.what()).c_str() );
        }
        if (!hSocket)
        {
            return false;
        }
        else    //if (hSocket)    // then it's OK
        {
            int
                nUrlLength = (int)strlen(pszTheFullUrl),
                nBytesSent;
            {
                nBytesSent = send(hSocket, pszTheFullUrl, nUrlLength, MSG_NOSIGNAL);
            }
            if (nBytesSent != nUrlLength )
            {
                printf(
                        "send() error: only sent %d of %d?"
                        "\n", 
                        nBytesSent,
                        nUrlLength
                      );
            }
            Sleep( nArbitraryShortTimeInMilliseconds );

            string
                strLine = "";

            bool 
                fLineOK = false;

            do
            {
                fLineOK = recvAline(hSocket, strLine);
                if (fShutdown)
                {
                    return false;
                }
                if (fLineOK)
                {
                    strBuffer += strLine;
                    if( string::npos != strLine.find( skey, 0 ) )
                    {
                        if(
                            ("" == skey)
                            ||
                            string::npos != strLine.find( skey, 0 ) 
                          ) 
                        {
                            string
                                sTemp;

                            if("" != skey)
                            {
                                if(
                                    ("USD" == skey)
                                    ||
                                    ("value" == skey)
                                  )
                                    sTemp = strLine.substr( strLine.find( skey, 0 ) + skey.size() + nOffset);
                                else
                                    sTemp = strLine.substr( strLine.find( skey, 0 ) + skey.size() + nOffset);
                            }
                            else
                                sTemp = strLine;

                            double 
                                dTemp;

                            if (1 == sscanf( sTemp.c_str(), "%lf", &dTemp ) )
                            {
                               dPrice = dTemp;      // just so I can debug.  A good compiler 
                                                    // can optimize this dTemp out!
                            }
                        }
                        // read rest of result
                        strLine = "";
                        do
                        {
                            fLineOK = recvAline(hSocket, strLine);
                            Sleep( nArbitraryShortTimeInMilliseconds ); // may not even be needed?
                            strLine = "";            
                        }
                        while( fLineOK );
                        break;
                    }
                }
                strLine = "";
            }
            while( fLineOK );
        }
    }
    if ( 0 < strBuffer.size() )
    {
        if (fPrintToConsole) 
        {
            printf(
                    "GetMyExternalWebPage() received:\n"
                    "%s"
                    "\n", 
                    strBuffer.c_str()
                  );
        }
        if( dPrice > 0.0 )
        {
            return true;
        }
        else
            return false;
    }
    else
    {
        return error("error in recv() : connection closed?");
    }
}
//_____________________________________________________________________________
static bool GetExternalWebPage(
                        CProvider & Cprovider,
                        string & strBuffer, 
                        double &dPriceRatio
                       )
{
    // we have all we need in Cprovider to get a price ratio,
    // first of YAC/BTC, then USD/BTC
    const string
        sLeadIn   = "GET ",
                    // here's where the api argument goes
        sPrologue = " HTTP/1.1"
                    "\r\n"
                    "Content-Type: text/html"
                    "\r\n"
                    "Accept: application/json, text/html"
                    "\r\n"
                    "Host: ",
                    // here's where the domain goes
        sEpilogue = "\r\n"
                    "Connection: close"
                    "\r\n"
                    "\r\n"
                    "";
    string
        sDomain          = Cprovider.sDomain,
        sPriceRatioKey   = Cprovider.sPriceRatioKey,
        sApi             = Cprovider.sApi;
    int
        nCharacterOffset = Cprovider.nOffset,
        nPort            = Cprovider.nPort;
    string
        sUrl = strprintf(
                         "%s%s%s%s%s",
                         sLeadIn.c_str(),
                         sApi.c_str(),
                         sPrologue.c_str(),
                         sDomain.c_str(),
                         sEpilogue.c_str()
                        );
    if (fPrintToConsole) 
    {
        string
            sfb = strprintf( "Command:\n%s\n", sUrl.c_str() );
        printf( "%s", sfb.c_str() );
    }
    const char
        *pszTheFullUrl = sUrl.c_str();
    bool
        fReturnValue = GetMyExternalWebPage( 
                                            sDomain, 
                                            sPriceRatioKey,
                                            pszTheFullUrl, 
                                            strBuffer, 
                                            dPriceRatio,
                                            nCharacterOffset,
                                            nPort
                                           );
    return fReturnValue;
}
//_____________________________________________________________________________
bool GetMyExternalWebPage1( int & nIndexBtcToYac, string & strBuffer, double & dPrice )
{
    CProvider 
        Cprovider;
    int 
        nSaved = nIndexBtcToYac,
        nSize = (int)vBTCtoYACProviders.size();
    do
    {
        Cprovider = vBTCtoYACProviders[ nIndexBtcToYac ];
        if (GetExternalWebPage( 
                                Cprovider,
                                strBuffer, 
                                dPrice
                              )
           )
        {
            break;
        }
        //else  // failure, so try another provider
        nIndexBtcToYac = (++nIndexBtcToYac < nSize)? nIndexBtcToYac: nIndexBtcToYac = 0;
        if( nSaved == nIndexBtcToYac )    // we can't find a provider, so quit
        {
            return error( "can't find a provider for page 1?" );
        }
    }while( true );
    return true;
}
//_____________________________________________________________________________

bool GetMyExternalWebPage2( int & nIndexUsdToBtc, string & strBuffer, double & dPrice )
{
    CProvider 
        Cprovider;
    int 
        nSaved = nIndexUsdToBtc,
        nSize = (int)vUSDtoBTCProviders.size();
    do
    {
        Cprovider = vUSDtoBTCProviders[ nIndexUsdToBtc ];
        if (GetExternalWebPage( 
                                Cprovider,
                                strBuffer, 
                                dPrice
                              )
           )
        {
            break;
        }
        //else  // failure, so try another provider
        nIndexUsdToBtc = (++nIndexUsdToBtc < nSize)? nIndexUsdToBtc: nIndexUsdToBtc = 0;
        if( nSaved == nIndexUsdToBtc )    // we can't find a provider, so quit
        {
            return error( "can't find a provider for page 2?" );
        }
    }while( true );

    return true;
}
//_____________________________________________________________________________
#endif
#ifdef _MSC_VER
    #include "msvc_warnings.pop.h"
#endif