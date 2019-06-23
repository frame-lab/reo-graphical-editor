const http = require('http');
const url = require('url');
const fs = require('fs');
const path = require('path');
var archiver = require('archiver');

var mimeTypes = {
    "html": "text/html",
    "jpeg": "image/jpeg",
    "jpg": "image/jpeg",
    "png": "image/png",
    "svg": "image/svg+xml",
    "js": "text/javascript",
    "css": "text/css",
    "treo": "text/treo"
};

http.createServer((request, response) => {
    var pathname = url.parse(request.url).pathname;
    var filename;
    if (pathname === '/nuXmv') {
        processPost(request, response, function () {
            fs.writeFileSync("./Reo2nuXmv/input.txt", request.post.content);

            const { exec } = require('child_process');
            exec('cd Reo2nuXmv && ./reo2nuXmv', (err, stdout, stderr) => {
                if (err) {
                    console.log(err);
                    response.write(err.message);
                    response.end(err.message);
                    return;
                }
                var archive = archiver('zip', {
                    gzip: true,
                    zlib: { level: 9 } // Sets the compression level.
                });
                archive.on('error', function (err) {
                    throw err;
                });
                // pipe archive data to the output file
                response.writeHead(200, {
                    'Content-Type': 'application/zip',
                    'Content-disposition': 'attachment; filename=myFile.zip'
                });
                archive.pipe(response);

                // append files
                archive.file('./Reo2nuXmv/nuxmv.smv', { name: 'componentProduct.txt' });
                archive.file('./Reo2nuXmv/nuxmv2.smv', { name: 'compactProduct.txt' });
                archive.finalize();
            });
        });
    } else {
        if (pathname === "/") {
            filename = "./public/index.html";
        }
        else
            filename = path.join('./public', pathname);
        try {
            fs.accessSync(filename, fs.F_OK);
            var fileStream = fs.createReadStream(filename);
            var mimeType = mimeTypes[path.extname(filename).split(".")[1]];
            response.writeHead(200, { 'Content-Type': mimeType });
            fileStream.pipe(response);
        }
        catch (e) {
            console.log('File not exists: ' + filename);
            response.writeHead(404, { 'Content-Type': 'text/plain' });
            response.write('404 Not Found\n');
            response.end();
            return;
        }
    }
    return;
}).listen(8081, '127.0.0.1');

console.log('Server running at http://127.0.0.1:8081/');

function processPost(request, response, callback) {
    var queryData = "";
    if (typeof callback !== 'function') return null;

    if (request.method == 'POST') {
        request.on('data', function (data) {
            queryData += data;
            if (queryData.length > 1e6) {
                queryData = "";
                response.writeHead(413, { 'Content-Type': 'text/plain' }).end();
                request.connection.destroy();
            }
        });

        request.on('end', function () {
            request.post = JSON.parse(queryData);
            callback();
        });

    } else {
        response.writeHead(405, { 'Content-Type': 'text/plain' });
        response.end();
    }
}

function zipper() {



}