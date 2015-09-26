#ifndef HMAC_H
#define HMAC_H

#include <string>
#include <map>
#include <sys/stat.h>
#include <string.h>

class  Random {
 public:
    unsigned long  seed;

    Random () {
	init ();
    };
    virtual  ~Random () {};
    void  init ();
    std::string  randomKey ();
 private:
    void  enc (unsigned long v, char* b);
};

class  HMacSignature {
 public:
    Random  rand;
    const char*  pathKeymap;
    struct stat  prevStat;
    std::string  slaveAccKey;
    int  sigAllowance;
    std::map<std::string, std::string>*  keymap;
    std::map<std::string, std::string>*  keymap_b;

    HMacSignature (const char* _path, int _sigallow): pathKeymap (_path), sigAllowance (_sigallow), keymap (NULL), keymap_b (NULL) {
	memset (&prevStat, 0, sizeof (prevStat));
    };
    virtual  ~HMacSignature () {
	delete keymap;
	delete keymap_b;
	keymap = NULL;
	keymap_b = NULL;
    };
    bool  loaddb ();
    bool  isActive () {
	return pathKeymap != NULL;
    };
    bool  slaveActive () {
	return slaveAccKey.size () > 0;
    };
    bool  find (const std::string& key, std::map<std::string, std::string>::const_iterator& i) {
	if (keymap) {
	    i = keymap->find (key);
	    return i != keymap->end ();
	} else {
	    return false;
	}
    };
    bool  inTime (time_t now, time_t tgt) {
	return now - sigAllowance <= tgt && tgt <= now + sigAllowance;
    };
 private:
    bool  checkKeymapStat ();
    void  loaddb_in ();
};

#define UCharConst(s)		(uchar_type(s)), (sizeof (s) - 1)
#define CharConst(s)		(s), (sizeof (s) - 1)
inline char*  char_type (u_char* v) {return (char*)v;}
inline char*  char_type (char* v) {return v;}
inline const char*  char_type (const u_char* v) {return (const char*)v;}
inline const u_char*  uchar_type (const char* v) {return (const u_char*)v;}

std::string  base64encode (const std::string& data);
std::string  base64decode (const std::string& data);
std::string  hmac_sha256 (const std::string& key, const std::string& data);
bool  readHttpDate (const std::string& date, uint64_t& t);

#endif /* HMAC_H */
