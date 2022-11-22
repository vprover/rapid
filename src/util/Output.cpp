#include "Output.hpp"

#include <fstream>
#include <iostream>
#include <string>

#include "Options.hpp"

namespace util {

std::ostream* Output::_stream = nullptr;

bool Output::_isFile = false;

int Output::_commentIndex = std::ios_base::xalloc();

bool Output::initialize() {
  _stream = &std::cout;
  return true;
}

void Output::close() {
  if (_isFile) {
    static_cast<std::ofstream*>(_stream)->close();
    _isFile = false;
  }
  _stream = nullptr;
}

void Output::error(std::string error) {
  assert(_stream);

  std::cerr << "ERROR: " << error << "\n";
}

void Output::warning(std::string warning) {
  assert(_stream);

  std::cerr << "WARNING: " << warning << "\n";
}

void Output::status(std::string status) {
  assert(_stream);

  //TODO check that _stream is not pointing to file
  *_stream << "#### Status: ##### " << status << "\n";
}

std::ostream& Output::comment(std::ostream& ostr) {
  if (ostr.iword(_commentIndex) != 1) {
    std::streambuf* buf = new CommentingStreambuf(ostr.rdbuf());
    ostr.rdbuf(buf);
    ostr.iword(_commentIndex) = 1;
  }
  return ostr;
}

std::ostream& Output::nocomment(std::ostream& ostr) {
  if (ostr.iword(_commentIndex) != 0) {
    CommentingStreambuf* cbuf = static_cast<CommentingStreambuf*>(ostr.rdbuf());
    std::streambuf* dest = cbuf->dest();
    ostr.rdbuf(dest);
    delete cbuf;
    ostr.iword(_commentIndex) = 0;
  }
  return ostr;
}

int CommentingStreambuf::overflow(int c) {
  if (c == EOF || !_dest) {
    return EOF;
  }
  if (_atLineStart) {
    if (util::Configuration::instance().tptp()) {
      _dest->sputc('%');
    } else {
      _dest->sputc(';');
    }
    _dest->sputc(' ');
    _atLineStart = false;
  }
  if (c == '\n') {
    _atLineStart = true;
  }
  return _dest->sputc(c);
}

}  // namespace util
