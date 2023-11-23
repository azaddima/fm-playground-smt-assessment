import React from 'react';

const PlainOutput = ({ code }) => {
  return (
    <pre id='info' style={{ backgroundColor: '#f4f4f4', padding: '1em', borderRadius: '8px', height: '60vh' }}>
      <code style={{ whiteSpace: 'pre-wrap' }}>{code}</code>
    </pre>
  );
};

export default PlainOutput;
